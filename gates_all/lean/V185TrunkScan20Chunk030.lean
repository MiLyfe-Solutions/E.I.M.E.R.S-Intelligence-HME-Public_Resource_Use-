import V185TrunkScan20Chunk029

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_182384 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_182384 : Nat := 118140960795 + 182384 * 2 ^ 59
def prefixEnd_182384 : Nat := 4983230072969 + 3 ^ 40 * 182384 * 2
def baseEnd_182384 : Nat := 83245027279750804854433

theorem tailTrace_182384 : CollatzResearch.WordTrace tailWord_182384 prefixEnd_182384 83245027279750804854433 := by
  unfold tailWord_182384
  simp only [CollatzResearch.WordTrace]
  refine ⟨3326045485630695776217103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4434727314174261034956137 3326045485630695776217103)
  ·
    refine ⟨4989068228446043664325655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3326045485630695776217103 4989068228446043664325655)
    ·
      refine ⟨7483602342669065496488483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4989068228446043664325655 7483602342669065496488483)
      ·
        refine ⟨11225403514003598244732725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7483602342669065496488483 11225403514003598244732725)
        ·
          refine ⟨1052381579437837335443693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11225403514003598244732725 1052381579437837335443693)
          ·
            refine ⟨394643092289189000791385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1052381579437837335443693 394643092289189000791385)
            ·
              refine ⟨295982319216891750593539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394643092289189000791385 295982319216891750593539)
              ·
                refine ⟨443973478825337625890309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295982319216891750593539 443973478825337625890309)
                ·
                  refine ⟨83245027279750804854433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 443973478825337625890309 83245027279750804854433)
                  ·
                    rfl

theorem cell20_182384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_182384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182384 prefixEnd_182384 := by exact prefixLift 182384
  have htrace : WordTrace (prefixWord ++ tailWord_182384) baseStart_182384 baseEnd_182384 := by
    simpa [prefixWord, tailWord_182384, baseEnd_182384] using wordTrace_append hprefix tailTrace_182384
  have hstable : (prefixWord ++ tailWord_182384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182384).length < 2 ^ (prefixWord ++ tailWord_182384).sum := by decide
  have hdescent : baseEnd_182384 < baseStart_182384 := by decide
  rcases family_descends (prefixWord ++ tailWord_182384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182408 : List Nat := [2, 1, 3, 4, 1, 1, 4, 4]
def baseStart_182408 : Nat := 118140960795 + 182408 * 2 ^ 59
def prefixEnd_182408 : Nat := 4983230072969 + 3 ^ 40 * 182408 * 2
def baseEnd_182408 : Nat := 27751993844571129351445

theorem tailTrace_182408 : CollatzResearch.WordTrace tailWord_182408 prefixEnd_182408 27751993844571129351445 := by
  unfold tailWord_182408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3326483161587221825653939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4435310882116295767538585 3326483161587221825653939)
  ·
    refine ⟨4989724742380832738480909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3326483161587221825653939 4989724742380832738480909)
    ·
      refine ⟨1871146778392812276930341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4989724742380832738480909 1871146778392812276930341)
      ·
        refine ⟨350840020948652301924439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1871146778392812276930341 350840020948652301924439)
        ·
          refine ⟨526260031422978452886659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350840020948652301924439 526260031422978452886659)
          ·
            refine ⟨789390047134467679329989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526260031422978452886659 789390047134467679329989)
            ·
              refine ⟨148010633837712689874373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 789390047134467679329989 148010633837712689874373)
              ·
                refine ⟨27751993844571129351445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148010633837712689874373 27751993844571129351445)
                ·
                  rfl

theorem cell20_182408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_182408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182408 prefixEnd_182408 := by exact prefixLift 182408
  have htrace : WordTrace (prefixWord ++ tailWord_182408) baseStart_182408 baseEnd_182408 := by
    simpa [prefixWord, tailWord_182408, baseEnd_182408] using wordTrace_append hprefix tailTrace_182408
  have hstable : (prefixWord ++ tailWord_182408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182408).length < 2 ^ (prefixWord ++ tailWord_182408).sum := by decide
  have hdescent : baseEnd_182408 < baseStart_182408 := by decide
  rcases family_descends (prefixWord ++ tailWord_182408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182429 : List Nat := [1, 4, 2, 1, 1, 5, 6]
def baseStart_182429 : Nat := 118140960795 + 182429 * 2 ^ 59
def prefixEnd_182429 : Nat := 4983230072969 + 3 ^ 40 * 182429 * 2
def baseEnd_182429 : Nat := 9251729611770072039361

theorem tailTrace_182429 : CollatzResearch.WordTrace tailWord_182429 prefixEnd_182429 9251729611770072039361 := by
  unfold tailWord_182429
  simp only [CollatzResearch.WordTrace]
  refine ⟨6653732256098364237822341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4435821504065576158548227 6653732256098364237822341)
  ·
    refine ⟨1247574798018443294591689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6653732256098364237822341 1247574798018443294591689)
    ·
      refine ⟨935681098513832470943767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1247574798018443294591689 935681098513832470943767)
      ·
        refine ⟨1403521647770748706415651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935681098513832470943767 1403521647770748706415651)
        ·
          refine ⟨2105282471656123059623477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403521647770748706415651 2105282471656123059623477)
          ·
            refine ⟨197370231717761536839701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2105282471656123059623477 197370231717761536839701)
            ·
              refine ⟨9251729611770072039361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197370231717761536839701 9251729611770072039361)
              ·
                rfl

theorem cell20_182429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 6].length) (baseStart_182429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182429 prefixEnd_182429 := by exact prefixLift 182429
  have htrace : WordTrace (prefixWord ++ tailWord_182429) baseStart_182429 baseEnd_182429 := by
    simpa [prefixWord, tailWord_182429, baseEnd_182429] using wordTrace_append hprefix tailTrace_182429
  have hstable : (prefixWord ++ tailWord_182429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182429).length < 2 ^ (prefixWord ++ tailWord_182429).sum := by decide
  have hdescent : baseEnd_182429 < baseStart_182429 := by decide
  rcases family_descends (prefixWord ++ tailWord_182429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182449 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 3]
def baseStart_182449 : Nat := 118140960795 + 182449 * 2 ^ 59
def prefixEnd_182449 : Nat := 4983230072969 + 3 ^ 40 * 182449 * 2
def baseEnd_182449 : Nat := 83274695050899467687501

theorem tailTrace_182449 : CollatzResearch.WordTrace tailWord_182449 prefixEnd_182449 83274695050899467687501 := by
  unfold tailWord_182449
  simp only [CollatzResearch.WordTrace]
  refine ⟨6654461716025907653550401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4436307810683938435700267 6654461716025907653550401)
  ·
    refine ⟨4990846287019430740162801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6654461716025907653550401 4990846287019430740162801)
    ·
      refine ⟨3743134715264573055122101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4990846287019430740162801 3743134715264573055122101)
      ·
        refine ⟨350918879556053723917697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3743134715264573055122101 350918879556053723917697)
        ·
          refine ⟨263189159667040292938273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350918879556053723917697 263189159667040292938273)
          ·
            refine ⟨197391869750280219703705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263189159667040292938273 197391869750280219703705)
            ·
              refine ⟨148043902312710164777779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197391869750280219703705 148043902312710164777779)
              ·
                refine ⟨222065853469065247166669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148043902312710164777779 222065853469065247166669)
                ·
                  refine ⟨83274695050899467687501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222065853469065247166669 83274695050899467687501)
                  ·
                    rfl

theorem cell20_182449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_182449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182449 prefixEnd_182449 := by exact prefixLift 182449
  have htrace : WordTrace (prefixWord ++ tailWord_182449) baseStart_182449 baseEnd_182449 := by
    simpa [prefixWord, tailWord_182449, baseEnd_182449] using wordTrace_append hprefix tailTrace_182449
  have hstable : (prefixWord ++ tailWord_182449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182449).length < 2 ^ (prefixWord ++ tailWord_182449).sum := by decide
  have hdescent : baseEnd_182449 < baseStart_182449 := by decide
  rcases family_descends (prefixWord ++ tailWord_182449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182488 : List Nat := [2, 1, 2, 2, 4, 9]
def baseStart_182488 : Nat := 118140960795 + 182488 * 2 ^ 59
def prefixEnd_182488 : Nat := 4983230072969 + 3 ^ 40 * 182488 * 2
def baseEnd_182488 : Nat := 3084907248651432051383

theorem tailTrace_182488 : CollatzResearch.WordTrace tailWord_182488 prefixEnd_182488 3084907248651432051383 := by
  unfold tailWord_182488
  simp only [CollatzResearch.WordTrace]
  refine ⟨3327942081442308657110059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4437256108589744876146745 3327942081442308657110059)
  ·
    refine ⟨4991913122163462985665089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3327942081442308657110059 4991913122163462985665089)
    ·
      refine ⟨3743934841622597239248817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4991913122163462985665089 3743934841622597239248817)
      ·
        refine ⟨2807951131216947929436613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3743934841622597239248817 2807951131216947929436613)
        ·
          refine ⟨526490837103177736769365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2807951131216947929436613 526490837103177736769365)
          ·
            refine ⟨3084907248651432051383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 526490837103177736769365 3084907248651432051383)
            ·
              rfl

theorem cell20_182488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 9].length) (baseStart_182488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182488 prefixEnd_182488 := by exact prefixLift 182488
  have htrace : WordTrace (prefixWord ++ tailWord_182488) baseStart_182488 baseEnd_182488 := by
    simpa [prefixWord, tailWord_182488, baseEnd_182488] using wordTrace_append hprefix tailTrace_182488
  have hstable : (prefixWord ++ tailWord_182488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182488).length < 2 ^ (prefixWord ++ tailWord_182488).sum := by decide
  have hdescent : baseEnd_182488 < baseStart_182488 := by decide
  rcases family_descends (prefixWord ++ tailWord_182488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182532 : List Nat := [2, 3, 2, 2, 3, 1, 2, 3, 2]
def baseStart_182532 : Nat := 118140960795 + 182532 * 2 ^ 59
def prefixEnd_182532 : Nat := 4983230072969 + 3 ^ 40 * 182532 * 2
def baseEnd_182532 : Nat := 83312578512520067920495

theorem tailTrace_182532 : CollatzResearch.WordTrace tailWord_182532 prefixEnd_182532 83312578512520067920495 := by
  unfold tailWord_182532
  simp only [CollatzResearch.WordTrace]
  refine ⟨3328744487362606414410925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4438325983150141885881233 3328744487362606414410925)
  ·
    refine ⟨1248279182760977405404097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3328744487362606414410925 1248279182760977405404097)
    ·
      refine ⟨936209387070733054053073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1248279182760977405404097 936209387070733054053073)
      ·
        refine ⟨702157040303049790539805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 936209387070733054053073 702157040303049790539805)
        ·
          refine ⟨263308890113643671452427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 702157040303049790539805 263308890113643671452427)
          ·
            refine ⟨394963335170465507178641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263308890113643671452427 394963335170465507178641)
            ·
              refine ⟨296222501377849130383981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394963335170465507178641 296222501377849130383981)
              ·
                refine ⟨111083438016693423893993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296222501377849130383981 111083438016693423893993)
                ·
                  refine ⟨83312578512520067920495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111083438016693423893993 83312578512520067920495)
                  ·
                    rfl

theorem cell20_182532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_182532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182532 prefixEnd_182532 := by exact prefixLift 182532
  have htrace : WordTrace (prefixWord ++ tailWord_182532) baseStart_182532 baseEnd_182532 := by
    simpa [prefixWord, tailWord_182532, baseEnd_182532] using wordTrace_append hprefix tailTrace_182532
  have hstable : (prefixWord ++ tailWord_182532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182532).length < 2 ^ (prefixWord ++ tailWord_182532).sum := by decide
  have hdescent : baseEnd_182532 < baseStart_182532 := by decide
  rcases family_descends (prefixWord ++ tailWord_182532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182577 : List Nat := [1, 2, 2, 3, 5, 1, 2, 4]
def baseStart_182577 : Nat := 118140960795 + 182577 * 2 ^ 59
def prefixEnd_182577 : Nat := 4983230072969 + 3 ^ 40 * 182577 * 2
def baseEnd_182577 : Nat := 27777705912899970473437

theorem tailTrace_182577 : CollatzResearch.WordTrace tailWord_182577 prefixEnd_182577 27777705912899970473437 := by
  unfold tailWord_182577
  simp only [CollatzResearch.WordTrace]
  refine ⟨6659130259562185514209985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4439420173041457009473323 6659130259562185514209985)
  ·
    refine ⟨4994347694671639135657489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6659130259562185514209985 4994347694671639135657489)
    ·
      refine ⟨3745760771003729351743117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4994347694671639135657489 3745760771003729351743117)
      ·
        refine ⟨1404660289126398506903669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3745760771003729351743117 1404660289126398506903669)
        ·
          refine ⟨131686902105599860022219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1404660289126398506903669 131686902105599860022219)
          ·
            refine ⟨197530353158399790033329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131686902105599860022219 197530353158399790033329)
            ·
              refine ⟨148147764868799842524997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197530353158399790033329 148147764868799842524997)
              ·
                refine ⟨27777705912899970473437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148147764868799842524997 27777705912899970473437)
                ·
                  rfl

theorem cell20_182577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 4].length) (baseStart_182577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182577 prefixEnd_182577 := by exact prefixLift 182577
  have htrace : WordTrace (prefixWord ++ tailWord_182577) baseStart_182577 baseEnd_182577 := by
    simpa [prefixWord, tailWord_182577, baseEnd_182577] using wordTrace_append hprefix tailTrace_182577
  have hstable : (prefixWord ++ tailWord_182577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182577).length < 2 ^ (prefixWord ++ tailWord_182577).sum := by decide
  have hdescent : baseEnd_182577 < baseStart_182577 := by decide
  rcases family_descends (prefixWord ++ tailWord_182577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182612 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_182612 : Nat := 118140960795 + 182612 * 2 ^ 59
def prefixEnd_182612 : Nat := 4983230072969 + 3 ^ 40 * 182612 * 2
def baseEnd_182612 : Nat := 83349092692395345253501

theorem tailTrace_182612 : CollatzResearch.WordTrace tailWord_182612 prefixEnd_182612 83349092692395345253501 := by
  unfold tailWord_182612
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330203407217693245867045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4440271209623590994489393 3330203407217693245867045)
  ·
    refine ⟨624413138853317483600071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3330203407217693245867045 624413138853317483600071)
    ·
      refine ⟨936619708279976225400107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 624413138853317483600071 936619708279976225400107)
      ·
        refine ⟨1404929562419964338100161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936619708279976225400107 1404929562419964338100161)
        ·
          refine ⟨1053697171814973253575121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1404929562419964338100161 1053697171814973253575121)
          ·
            refine ⟨790272878861229940181341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1053697171814973253575121 790272878861229940181341)
            ·
              refine ⟨296352329572961227568003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 790272878861229940181341 296352329572961227568003)
              ·
                refine ⟨444528494359441841352005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296352329572961227568003 444528494359441841352005)
                ·
                  refine ⟨83349092692395345253501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 444528494359441841352005 83349092692395345253501)
                  ·
                    rfl

theorem cell20_182612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_182612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182612 prefixEnd_182612 := by exact prefixLift 182612
  have htrace : WordTrace (prefixWord ++ tailWord_182612) baseStart_182612 baseEnd_182612 := by
    simpa [prefixWord, tailWord_182612, baseEnd_182612] using wordTrace_append hprefix tailTrace_182612
  have hstable : (prefixWord ++ tailWord_182612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182612).length < 2 ^ (prefixWord ++ tailWord_182612).sum := by decide
  have hdescent : baseEnd_182612 < baseStart_182612 := by decide
  rcases family_descends (prefixWord ++ tailWord_182612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182640 : List Nat := [2, 1, 1, 1, 4, 3, 2, 6]
def baseStart_182640 : Nat := 118140960795 + 182640 * 2 ^ 59
def prefixEnd_182640 : Nat := 4983230072969 + 3 ^ 40 * 182640 * 2
def baseEnd_182640 : Nat := 27787290885117230773351

theorem tailTrace_182640 : CollatzResearch.WordTrace tailWord_182640 prefixEnd_182640 27787290885117230773351 := by
  unfold tailWord_182640
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330714029166973636876687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4440952038889298182502249 3330714029166973636876687)
  ·
    refine ⟨4996071043750460455315031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3330714029166973636876687 4996071043750460455315031)
    ·
      refine ⟨7494106565625690682972547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4996071043750460455315031 7494106565625690682972547)
      ·
        refine ⟨11241159848438536024458821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7494106565625690682972547 11241159848438536024458821)
        ·
          refine ⟨2107717471582225504586029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11241159848438536024458821 2107717471582225504586029)
          ·
            refine ⟨790394051843334564219761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2107717471582225504586029 790394051843334564219761)
            ·
              refine ⟨592795538882500923164821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790394051843334564219761 592795538882500923164821)
              ·
                refine ⟨27787290885117230773351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 592795538882500923164821 27787290885117230773351)
                ·
                  rfl

theorem cell20_182640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_182640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182640 prefixEnd_182640 := by exact prefixLift 182640
  have htrace : WordTrace (prefixWord ++ tailWord_182640) baseStart_182640 baseEnd_182640 := by
    simpa [prefixWord, tailWord_182640, baseEnd_182640] using wordTrace_append hprefix tailTrace_182640
  have hstable : (prefixWord ++ tailWord_182640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182640).length < 2 ^ (prefixWord ++ tailWord_182640).sum := by decide
  have hdescent : baseEnd_182640 < baseStart_182640 := by decide
  rcases family_descends (prefixWord ++ tailWord_182640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182647 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_182647 : Nat := 118140960795 + 182647 * 2 ^ 59
def prefixEnd_182647 : Nat := 4983230072969 + 3 ^ 40 * 182647 * 2
def baseEnd_182647 : Nat := 83365067646090779086691

theorem tailTrace_182647 : CollatzResearch.WordTrace tailWord_182647 prefixEnd_182647 83365067646090779086691 := by
  unfold tailWord_182647
  simp only [CollatzResearch.WordTrace]
  refine ⟨6661683369308587469258195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4441122246205724979505463 6661683369308587469258195)
  ·
    refine ⟨9992525053962881203887293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6661683369308587469258195 9992525053962881203887293)
    ·
      refine ⟨3747196895236080451457735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9992525053962881203887293 3747196895236080451457735)
      ·
        refine ⟨5620795342854120677186603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3747196895236080451457735 5620795342854120677186603)
        ·
          refine ⟨8431193014281181015779905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5620795342854120677186603 8431193014281181015779905)
          ·
            refine ⟨6323394760710885761834929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8431193014281181015779905 6323394760710885761834929)
            ·
              refine ⟨4742546070533164321376197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6323394760710885761834929 4742546070533164321376197)
              ·
                refine ⟨889227388224968310258037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4742546070533164321376197 889227388224968310258037)
                ·
                  refine ⟨83365067646090779086691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 889227388224968310258037 83365067646090779086691)
                  ·
                    rfl

theorem cell20_182647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_182647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182647 prefixEnd_182647 := by exact prefixLift 182647
  have htrace : WordTrace (prefixWord ++ tailWord_182647) baseStart_182647 baseEnd_182647 := by
    simpa [prefixWord, tailWord_182647, baseEnd_182647] using wordTrace_append hprefix tailTrace_182647
  have hstable : (prefixWord ++ tailWord_182647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182647).length < 2 ^ (prefixWord ++ tailWord_182647).sum := by decide
  have hdescent : baseEnd_182647 < baseStart_182647 := by decide
  rcases family_descends (prefixWord ++ tailWord_182647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182667 : List Nat := [1, 1, 1, 1, 4, 4, 4, 2, 2]
def baseStart_182667 : Nat := 118140960795 + 182667 * 2 ^ 59
def prefixEnd_182667 : Nat := 4983230072969 + 3 ^ 40 * 182667 * 2
def baseEnd_182667 : Nat := 83374196191059598419943

theorem tailTrace_182667 : CollatzResearch.WordTrace tailWord_182667 prefixEnd_182667 83374196191059598419943 := by
  unfold tailWord_182667
  simp only [CollatzResearch.WordTrace]
  refine ⟨6662412829236130884986255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4441608552824087256657503 6662412829236130884986255)
  ·
    refine ⟨9993619243854196327479383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6662412829236130884986255 9993619243854196327479383)
    ·
      refine ⟨14990428865781294491219075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9993619243854196327479383 14990428865781294491219075)
      ·
        refine ⟨22485643298671941736828613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14990428865781294491219075 22485643298671941736828613)
        ·
          refine ⟨4216058118500989075655365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22485643298671941736828613 4216058118500989075655365)
          ·
            refine ⟨790510897218935451685381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4216058118500989075655365 790510897218935451685381)
            ·
              refine ⟨148220793228550397191009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 790510897218935451685381 148220793228550397191009)
              ·
                refine ⟨111165594921412797893257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148220793228550397191009 111165594921412797893257)
                ·
                  refine ⟨83374196191059598419943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111165594921412797893257 83374196191059598419943)
                  ·
                    rfl

theorem cell20_182667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 2].length) (baseStart_182667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182667 prefixEnd_182667 := by exact prefixLift 182667
  have htrace : WordTrace (prefixWord ++ tailWord_182667) baseStart_182667 baseEnd_182667 := by
    simpa [prefixWord, tailWord_182667, baseEnd_182667] using wordTrace_append hprefix tailTrace_182667
  have hstable : (prefixWord ++ tailWord_182667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182667).length < 2 ^ (prefixWord ++ tailWord_182667).sum := by decide
  have hdescent : baseEnd_182667 < baseStart_182667 := by decide
  rcases family_descends (prefixWord ++ tailWord_182667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182705 : List Nat := [1, 2, 2, 4, 1, 3, 2, 3, 2]
def baseStart_182705 : Nat := 118140960795 + 182705 * 2 ^ 59
def prefixEnd_182705 : Nat := 4983230072969 + 3 ^ 40 * 182705 * 2
def baseEnd_182705 : Nat := 83391540426500355153121

theorem tailTrace_182705 : CollatzResearch.WordTrace tailWord_182705 prefixEnd_182705 83391540426500355153121 := by
  unfold tailWord_182705
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663798803098463374869569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4442532535398975583246379 6663798803098463374869569)
  ·
    refine ⟨4997849102323847531152177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6663798803098463374869569 4997849102323847531152177)
    ·
      refine ⟨3748386826742885648364133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4997849102323847531152177 3748386826742885648364133)
      ·
        refine ⟨702822530014291059068275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3748386826742885648364133 702822530014291059068275)
        ·
          refine ⟨1054233795021436588602413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702822530014291059068275 1054233795021436588602413)
          ·
            refine ⟨395337673133038720725905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1054233795021436588602413 395337673133038720725905)
            ·
              refine ⟨296503254849779040544429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395337673133038720725905 296503254849779040544429)
              ·
                refine ⟨111188720568667140204161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296503254849779040544429 111188720568667140204161)
                ·
                  refine ⟨83391540426500355153121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111188720568667140204161 83391540426500355153121)
                  ·
                    rfl

theorem cell20_182705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 2].length) (baseStart_182705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182705 prefixEnd_182705 := by exact prefixLift 182705
  have htrace : WordTrace (prefixWord ++ tailWord_182705) baseStart_182705 baseEnd_182705 := by
    simpa [prefixWord, tailWord_182705, baseEnd_182705] using wordTrace_append hprefix tailTrace_182705
  have hstable : (prefixWord ++ tailWord_182705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182705).length < 2 ^ (prefixWord ++ tailWord_182705).sum := by decide
  have hdescent : baseEnd_182705 < baseStart_182705 := by decide
  rcases family_descends (prefixWord ++ tailWord_182705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182781 : List Nat := [1, 4, 1, 1, 1, 3, 5, 2, 2]
def baseStart_182781 : Nat := 118140960795 + 182781 * 2 ^ 59
def prefixEnd_182781 : Nat := 4983230072969 + 3 ^ 40 * 182781 * 2
def baseEnd_182781 : Nat := 83426228897381868619477

theorem tailTrace_182781 : CollatzResearch.WordTrace tailWord_182781 prefixEnd_182781 83426228897381868619477 := by
  unfold tailWord_182781
  simp only [CollatzResearch.WordTrace]
  refine ⟨6666570750823128354636197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4444380500548752236424131 6666570750823128354636197)
  ·
    refine ⟨1249982015779336566494287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6666570750823128354636197 1249982015779336566494287)
    ·
      refine ⟨1874973023669004849741431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1249982015779336566494287 1874973023669004849741431)
      ·
        refine ⟨2812459535503507274612147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874973023669004849741431 2812459535503507274612147)
        ·
          refine ⟨4218689303255260911918221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2812459535503507274612147 4218689303255260911918221)
          ·
            refine ⟨1582008488720722841969333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4218689303255260911918221 1582008488720722841969333)
            ·
              refine ⟨148313295817567766434625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1582008488720722841969333 148313295817567766434625)
              ·
                refine ⟨111234971863175824825969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148313295817567766434625 111234971863175824825969)
                ·
                  refine ⟨83426228897381868619477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111234971863175824825969 83426228897381868619477)
                  ·
                    rfl

theorem cell20_182781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_182781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182781 prefixEnd_182781 := by exact prefixLift 182781
  have htrace : WordTrace (prefixWord ++ tailWord_182781) baseStart_182781 baseEnd_182781 := by
    simpa [prefixWord, tailWord_182781, baseEnd_182781] using wordTrace_append hprefix tailTrace_182781
  have hstable : (prefixWord ++ tailWord_182781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182781).length < 2 ^ (prefixWord ++ tailWord_182781).sum := by decide
  have hdescent : baseEnd_182781 < baseStart_182781 := by decide
  rcases family_descends (prefixWord ++ tailWord_182781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182791 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 3]
def baseStart_182791 : Nat := 118140960795 + 182791 * 2 ^ 59
def prefixEnd_182791 : Nat := 4983230072969 + 3 ^ 40 * 182791 * 2
def baseEnd_182791 : Nat := 83430793169866278286103

theorem tailTrace_182791 : CollatzResearch.WordTrace tailWord_182791 prefixEnd_182791 83430793169866278286103 := by
  unfold tailWord_182791
  simp only [CollatzResearch.WordTrace]
  refine ⟨6666935480786900062500227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4444623653857933375000151 6666935480786900062500227)
  ·
    refine ⟨10000403221180350093750341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6666935480786900062500227 10000403221180350093750341)
    ·
      refine ⟨1875075603971315642578189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10000403221180350093750341 1875075603971315642578189)
      ·
        refine ⟨703153351489243365966821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1875075603971315642578189 703153351489243365966821)
        ·
          refine ⟨131841253404233131118779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 703153351489243365966821 131841253404233131118779)
          ·
            refine ⟨197761880106349696678169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131841253404233131118779 197761880106349696678169)
            ·
              refine ⟨148321410079762272508627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197761880106349696678169 148321410079762272508627)
              ·
                refine ⟨222482115119643408762941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148321410079762272508627 222482115119643408762941)
                ·
                  refine ⟨83430793169866278286103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222482115119643408762941 83430793169866278286103)
                  ·
                    rfl

theorem cell20_182791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 3].length) (baseStart_182791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182791 prefixEnd_182791 := by exact prefixLift 182791
  have htrace : WordTrace (prefixWord ++ tailWord_182791) baseStart_182791 baseEnd_182791 := by
    simpa [prefixWord, tailWord_182791, baseEnd_182791] using wordTrace_append hprefix tailTrace_182791
  have hstable : (prefixWord ++ tailWord_182791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182791).length < 2 ^ (prefixWord ++ tailWord_182791).sum := by decide
  have hdescent : baseEnd_182791 < baseStart_182791 := by decide
  rcases family_descends (prefixWord ++ tailWord_182791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182795 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 3]
def baseStart_182795 : Nat := 118140960795 + 182795 * 2 ^ 59
def prefixEnd_182795 : Nat := 4983230072969 + 3 ^ 40 * 182795 * 2
def baseEnd_182795 : Nat := 83432618878860042152753

theorem tailTrace_182795 : CollatzResearch.WordTrace tailWord_182795 prefixEnd_182795 83432618878860042152753 := by
  unfold tailWord_182795
  simp only [CollatzResearch.WordTrace]
  refine ⟨6667081372772408745645839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4444720915181605830430559 6667081372772408745645839)
  ·
    refine ⟨10000622059158613118468759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6667081372772408745645839 10000622059158613118468759)
    ·
      refine ⟨15000933088737919677703139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10000622059158613118468759 15000933088737919677703139)
      ·
        refine ⟨22501399633106879516554709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15000933088737919677703139 22501399633106879516554709)
        ·
          refine ⟨527376553900942488669251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 22501399633106879516554709 527376553900942488669251)
          ·
            refine ⟨791064830851413733003877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527376553900942488669251 791064830851413733003877)
            ·
              refine ⟨148324655784640074938227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 791064830851413733003877 148324655784640074938227)
              ·
                refine ⟨222486983676960112407341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148324655784640074938227 222486983676960112407341)
                ·
                  refine ⟨83432618878860042152753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222486983676960112407341 83432618878860042152753)
                  ·
                    rfl

theorem cell20_182795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 3].length) (baseStart_182795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182795 prefixEnd_182795 := by exact prefixLift 182795
  have htrace : WordTrace (prefixWord ++ tailWord_182795) baseStart_182795 baseEnd_182795 := by
    simpa [prefixWord, tailWord_182795, baseEnd_182795] using wordTrace_append hprefix tailTrace_182795
  have hstable : (prefixWord ++ tailWord_182795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182795).length < 2 ^ (prefixWord ++ tailWord_182795).sum := by decide
  have hdescent : baseEnd_182795 < baseStart_182795 := by decide
  rcases family_descends (prefixWord ++ tailWord_182795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182830 : List Nat := [4, 1, 3, 1, 11]
def baseStart_182830 : Nat := 118140960795 + 182830 * 2 ^ 59
def prefixEnd_182830 : Nat := 4983230072969 + 3 ^ 40 * 182830 * 2
def baseEnd_182830 : Nat := 1030229553488339209703

theorem tailTrace_182830 : CollatzResearch.WordTrace tailWord_182830 prefixEnd_182830 1030229553488339209703 := by
  unfold tailWord_182830
  simp only [CollatzResearch.WordTrace]
  refine ⟨833544740955701215396243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4445571951763739815446629 833544740955701215396243)
  ·
    refine ⟨1250317111433551823094365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833544740955701215396243 1250317111433551823094365)
    ·
      refine ⟨468868916787581933660387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1250317111433551823094365 468868916787581933660387)
      ·
        refine ⟨703303375181372900490581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468868916787581933660387 703303375181372900490581)
        ·
          refine ⟨1030229553488339209703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 703303375181372900490581 1030229553488339209703)
          ·
            rfl

theorem cell20_182830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 11].length) (baseStart_182830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182830 prefixEnd_182830 := by exact prefixLift 182830
  have htrace : WordTrace (prefixWord ++ tailWord_182830) baseStart_182830 baseEnd_182830 := by
    simpa [prefixWord, tailWord_182830, baseEnd_182830] using wordTrace_append hprefix tailTrace_182830
  have hstable : (prefixWord ++ tailWord_182830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182830).length < 2 ^ (prefixWord ++ tailWord_182830).sum := by decide
  have hdescent : baseEnd_182830 < baseStart_182830 := by decide
  rcases family_descends (prefixWord ++ tailWord_182830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182840 : List Nat := [2, 1, 2, 1, 4, 1, 3, 4, 2]
def baseStart_182840 : Nat := 118140960795 + 182840 * 2 ^ 59
def prefixEnd_182840 : Nat := 4983230072969 + 3 ^ 40 * 182840 * 2
def baseEnd_182840 : Nat := 83453158105039885652569

theorem tailTrace_182840 : CollatzResearch.WordTrace tailWord_182840 prefixEnd_182840 83453158105039885652569 := by
  unfold tailWord_182840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334361328804690715516987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4445815105072920954022649 3334361328804690715516987)
  ·
    refine ⟨5001541993207036073275481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3334361328804690715516987 5001541993207036073275481)
    ·
      refine ⟨3751156494905277054956611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5001541993207036073275481 3751156494905277054956611)
      ·
        refine ⟨5626734742357915582434917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751156494905277054956611 5626734742357915582434917)
        ·
          refine ⟨1055012764192109171706547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5626734742357915582434917 1055012764192109171706547)
          ·
            refine ⟨1582519146288163757559821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055012764192109171706547 1582519146288163757559821)
            ·
              refine ⟨593444679858061409084933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1582519146288163757559821 593444679858061409084933)
              ·
                refine ⟨111270877473386514203425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 593444679858061409084933 111270877473386514203425)
                ·
                  refine ⟨83453158105039885652569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111270877473386514203425 83453158105039885652569)
                  ·
                    rfl

theorem cell20_182840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 2].length) (baseStart_182840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182840 prefixEnd_182840 := by exact prefixLift 182840
  have htrace : WordTrace (prefixWord ++ tailWord_182840) baseStart_182840 baseEnd_182840 := by
    simpa [prefixWord, tailWord_182840, baseEnd_182840] using wordTrace_append hprefix tailTrace_182840
  have hstable : (prefixWord ++ tailWord_182840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182840).length < 2 ^ (prefixWord ++ tailWord_182840).sum := by decide
  have hdescent : baseEnd_182840 < baseStart_182840 := by decide
  rcases family_descends (prefixWord ++ tailWord_182840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182888 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 3]
def baseStart_182888 : Nat := 118140960795 + 182888 * 2 ^ 59
def prefixEnd_182888 : Nat := 4983230072969 + 3 ^ 40 * 182888 * 2
def baseEnd_182888 : Nat := 83475066612965052052373

theorem tailTrace_182888 : CollatzResearch.WordTrace tailWord_182888 prefixEnd_182888 83475066612965052052373 := by
  unfold tailWord_182888
  simp only [CollatzResearch.WordTrace]
  refine ⟨3335236680717742814390659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4446982240956990419187545 3335236680717742814390659)
  ·
    refine ⟨5002855021076614221585989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3335236680717742814390659 5002855021076614221585989)
    ·
      refine ⟨938035316451865166547373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5002855021076614221585989 938035316451865166547373)
      ·
        refine ⟨351763243669449437455265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 938035316451865166547373 351763243669449437455265)
        ·
          refine ⟨263822432752087078091449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351763243669449437455265 263822432752087078091449)
          ·
            refine ⟨197866824564065308568587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263822432752087078091449 197866824564065308568587)
            ·
              refine ⟨296800236846097962852881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197866824564065308568587 296800236846097962852881)
              ·
                refine ⟨222600177634573472139661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296800236846097962852881 222600177634573472139661)
                ·
                  refine ⟨83475066612965052052373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222600177634573472139661 83475066612965052052373)
                  ·
                    rfl

theorem cell20_182888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_182888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182888 prefixEnd_182888 := by exact prefixLift 182888
  have htrace : WordTrace (prefixWord ++ tailWord_182888) baseStart_182888 baseEnd_182888 := by
    simpa [prefixWord, tailWord_182888, baseEnd_182888] using wordTrace_append hprefix tailTrace_182888
  have hstable : (prefixWord ++ tailWord_182888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182888).length < 2 ^ (prefixWord ++ tailWord_182888).sum := by decide
  have hdescent : baseEnd_182888 < baseStart_182888 := by decide
  rcases family_descends (prefixWord ++ tailWord_182888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182892 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 3]
def baseStart_182892 : Nat := 118140960795 + 182892 * 2 ^ 59
def prefixEnd_182892 : Nat := 4983230072969 + 3 ^ 40 * 182892 * 2
def baseEnd_182892 : Nat := 83476892321958815919023

theorem tailTrace_182892 : CollatzResearch.WordTrace tailWord_182892 prefixEnd_182892 83476892321958815919023 := by
  unfold tailWord_182892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3335309626710497155963465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4447079502280662874617953 3335309626710497155963465)
  ·
    refine ⟨2501482220032872866972599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3335309626710497155963465 2501482220032872866972599)
    ·
      refine ⟨3752223330049309300458899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2501482220032872866972599 3752223330049309300458899)
      ·
        refine ⟨5628334995073963950688349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3752223330049309300458899 5628334995073963950688349)
        ·
          refine ⟨2110625623152736481508131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5628334995073963950688349 2110625623152736481508131)
          ·
            refine ⟨3165938434729104722262197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110625623152736481508131 3165938434729104722262197)
            ·
              refine ⟨296806728255853567712081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3165938434729104722262197 296806728255853567712081)
              ·
                refine ⟨222605046191890175784061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296806728255853567712081 222605046191890175784061)
                ·
                  refine ⟨83476892321958815919023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222605046191890175784061 83476892321958815919023)
                  ·
                    rfl

theorem cell20_182892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_182892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182892 prefixEnd_182892 := by exact prefixLift 182892
  have htrace : WordTrace (prefixWord ++ tailWord_182892) baseStart_182892 baseEnd_182892 := by
    simpa [prefixWord, tailWord_182892, baseEnd_182892] using wordTrace_append hprefix tailTrace_182892
  have hstable : (prefixWord ++ tailWord_182892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182892).length < 2 ^ (prefixWord ++ tailWord_182892).sum := by decide
  have hdescent : baseEnd_182892 < baseStart_182892 := by decide
  rcases family_descends (prefixWord ++ tailWord_182892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182927 : List Nat := [1, 1, 2, 1, 1, 1, 1, 12]
def baseStart_182927 : Nat := 118140960795 + 182927 * 2 ^ 59
def prefixEnd_182927 : Nat := 4983230072969 + 3 ^ 40 * 182927 * 2
def baseEnd_182927 : Nat := 27830955758551416584071

theorem tailTrace_182927 : CollatzResearch.WordTrace tailWord_182927 prefixEnd_182927 27830955758551416584071 := by
  unfold tailWord_182927
  simp only [CollatzResearch.WordTrace]
  refine ⟨6671895808294195289451035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4447930538862796859634023 6671895808294195289451035)
  ·
    refine ⟨10007843712441292934176553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6671895808294195289451035 10007843712441292934176553)
    ·
      refine ⟨7505882784330969700632415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10007843712441292934176553 7505882784330969700632415)
      ·
        refine ⟨11258824176496454550948623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7505882784330969700632415 11258824176496454550948623)
        ·
          refine ⟨16888236264744681826422935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11258824176496454550948623 16888236264744681826422935)
          ·
            refine ⟨25332354397117022739634403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16888236264744681826422935 25332354397117022739634403)
            ·
              refine ⟨37998531595675534109451605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25332354397117022739634403 37998531595675534109451605)
              ·
                refine ⟨27830955758551416584071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 37998531595675534109451605 27830955758551416584071)
                ·
                  rfl

theorem cell20_182927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_182927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182927 prefixEnd_182927 := by exact prefixLift 182927
  have htrace : WordTrace (prefixWord ++ tailWord_182927) baseStart_182927 baseEnd_182927 := by
    simpa [prefixWord, tailWord_182927, baseEnd_182927] using wordTrace_append hprefix tailTrace_182927
  have hstable : (prefixWord ++ tailWord_182927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182927).length < 2 ^ (prefixWord ++ tailWord_182927).sum := by decide
  have hdescent : baseEnd_182927 < baseStart_182927 := by decide
  rcases family_descends (prefixWord ++ tailWord_182927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182930 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_182930 : Nat := 118140960795 + 182930 * 2 ^ 59
def prefixEnd_182930 : Nat := 4983230072969 + 3 ^ 40 * 182930 * 2
def baseEnd_182930 : Nat := 83494236557399572652201

theorem tailTrace_182930 : CollatzResearch.WordTrace tailWord_182930 prefixEnd_182930 83494236557399572652201 := by
  unfold tailWord_182930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668001306820831700452561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4448003484855551201206829 1668001306820831700452561)
  ·
    refine ⟨1251000980115623775339421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1668001306820831700452561 1251000980115623775339421)
    ·
      refine ⟨469125367543358915752283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1251000980115623775339421 469125367543358915752283)
      ·
        refine ⟨703688051315038373628425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469125367543358915752283 703688051315038373628425)
        ·
          refine ⟨527766038486278780221319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 703688051315038373628425 527766038486278780221319)
          ·
            refine ⟨791649057729418170331979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527766038486278780221319 791649057729418170331979)
            ·
              refine ⟨1187473586594127255497969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791649057729418170331979 1187473586594127255497969)
              ·
                refine ⟨890605189945595441623477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1187473586594127255497969 890605189945595441623477)
                ·
                  refine ⟨83494236557399572652201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 890605189945595441623477 83494236557399572652201)
                  ·
                    rfl

theorem cell20_182930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_182930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182930 prefixEnd_182930 := by exact prefixLift 182930
  have htrace : WordTrace (prefixWord ++ tailWord_182930) baseStart_182930 baseEnd_182930 := by
    simpa [prefixWord, tailWord_182930, baseEnd_182930] using wordTrace_append hprefix tailTrace_182930
  have hstable : (prefixWord ++ tailWord_182930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182930).length < 2 ^ (prefixWord ++ tailWord_182930).sum := by decide
  have hdescent : baseEnd_182930 < baseStart_182930 := by decide
  rcases family_descends (prefixWord ++ tailWord_182930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183009 : List Nat := [1, 2, 3, 1, 4, 1, 4, 2, 2]
def baseStart_183009 : Nat := 118140960795 + 183009 * 2 ^ 59
def prefixEnd_183009 : Nat := 4983230072969 + 3 ^ 40 * 183009 * 2
def baseEnd_183009 : Nat := 83530294310026409018545

theorem tailTrace_183009 : CollatzResearch.WordTrace tailWord_183009 prefixEnd_183009 83530294310026409018545 := by
  unfold tailWord_183009
  simp only [CollatzResearch.WordTrace]
  refine ⟨6674886593997123293936081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4449924395998082195957387 6674886593997123293936081)
  ·
    refine ⟨5006164945497842470452061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6674886593997123293936081 5006164945497842470452061)
    ·
      refine ⟨1877311854561690926419523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5006164945497842470452061 1877311854561690926419523)
      ·
        refine ⟨2815967781842536389629285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1877311854561690926419523 2815967781842536389629285)
        ·
          refine ⟨527993959095475573055491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2815967781842536389629285 527993959095475573055491)
          ·
            refine ⟨791990938643213359583237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527993959095475573055491 791990938643213359583237)
            ·
              refine ⟨148498300995602504921857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 791990938643213359583237 148498300995602504921857)
              ·
                refine ⟨111373725746701878691393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148498300995602504921857 111373725746701878691393)
                ·
                  refine ⟨83530294310026409018545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111373725746701878691393 83530294310026409018545)
                  ·
                    rfl

theorem cell20_183009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 2].length) (baseStart_183009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183009 prefixEnd_183009 := by exact prefixLift 183009
  have htrace : WordTrace (prefixWord ++ tailWord_183009) baseStart_183009 baseEnd_183009 := by
    simpa [prefixWord, tailWord_183009, baseEnd_183009] using wordTrace_append hprefix tailTrace_183009
  have hstable : (prefixWord ++ tailWord_183009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183009).length < 2 ^ (prefixWord ++ tailWord_183009).sum := by decide
  have hdescent : baseEnd_183009 < baseStart_183009 := by decide
  rcases family_descends (prefixWord ++ tailWord_183009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183016 : List Nat := [2, 1, 4, 1, 5, 1, 1, 5]
def baseStart_183016 : Nat := 118140960795 + 183016 * 2 ^ 59
def prefixEnd_183016 : Nat := 4983230072969 + 3 ^ 40 * 183016 * 2
def baseEnd_183016 : Nat := 27844496433588498595061

theorem tailTrace_183016 : CollatzResearch.WordTrace tailWord_183016 prefixEnd_183016 27844496433588498595061 := by
  unfold tailWord_183016
  simp only [CollatzResearch.WordTrace]
  refine ⟨3337570952485881744720451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4450094603314508992960601 3337570952485881744720451)
  ·
    refine ⟨5006356428728822617080677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3337570952485881744720451 5006356428728822617080677)
    ·
      refine ⟨938691830386654240702627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5006356428728822617080677 938691830386654240702627)
      ·
        refine ⟨1408037745579981361053941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 938691830386654240702627 1408037745579981361053941)
        ·
          refine ⟨132003538648123252598807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1408037745579981361053941 132003538648123252598807)
          ·
            refine ⟨198005307972184878898211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132003538648123252598807 198005307972184878898211)
            ·
              refine ⟨297007961958277318347317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198005307972184878898211 297007961958277318347317)
              ·
                refine ⟨27844496433588498595061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 297007961958277318347317 27844496433588498595061)
                ·
                  rfl

theorem cell20_183016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_183016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183016 prefixEnd_183016 := by exact prefixLift 183016
  have htrace : WordTrace (prefixWord ++ tailWord_183016) baseStart_183016 baseEnd_183016 := by
    simpa [prefixWord, tailWord_183016, baseEnd_183016] using wordTrace_append hprefix tailTrace_183016
  have hstable : (prefixWord ++ tailWord_183016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183016).length < 2 ^ (prefixWord ++ tailWord_183016).sum := by decide
  have hdescent : baseEnd_183016 < baseStart_183016 := by decide
  rcases family_descends (prefixWord ++ tailWord_183016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183034 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_183034 : Nat := 118140960795 + 183034 * 2 ^ 59
def prefixEnd_183034 : Nat := 4983230072969 + 3 ^ 40 * 183034 * 2
def baseEnd_183034 : Nat := 83541704991237433185109

theorem tailTrace_183034 : CollatzResearch.WordTrace tailWord_183034 prefixEnd_183034 83541704991237433185109 := by
  unfold tailWord_183034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668949604726638140899039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4450532279271035042397437 1668949604726638140899039)
  ·
    refine ⟨2503424407089957211348559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1668949604726638140899039 2503424407089957211348559)
    ·
      refine ⟨3755136610634935817022839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2503424407089957211348559 3755136610634935817022839)
      ·
        refine ⟨5632704915952403725534259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3755136610634935817022839 5632704915952403725534259)
        ·
          refine ⟨8449057373928605588301389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5632704915952403725534259 8449057373928605588301389)
          ·
            refine ⟨3168396515223227095613021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8449057373928605588301389 3168396515223227095613021)
            ·
              refine ⟨1188148693208710160854883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3168396515223227095613021 1188148693208710160854883)
              ·
                refine ⟨1782223039813065241282325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188148693208710160854883 1782223039813065241282325)
                ·
                  refine ⟨83541704991237433185109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1782223039813065241282325 83541704991237433185109)
                  ·
                    rfl

theorem cell20_183034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_183034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183034 prefixEnd_183034 := by exact prefixLift 183034
  have htrace : WordTrace (prefixWord ++ tailWord_183034) baseStart_183034 baseEnd_183034 := by
    simpa [prefixWord, tailWord_183034, baseEnd_183034] using wordTrace_append hprefix tailTrace_183034
  have hstable : (prefixWord ++ tailWord_183034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183034).length < 2 ^ (prefixWord ++ tailWord_183034).sum := by decide
  have hdescent : baseEnd_183034 < baseStart_183034 := by decide
  rcases family_descends (prefixWord ++ tailWord_183034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183047 : List Nat := [1, 1, 4, 4, 1, 2, 2, 3, 2]
def baseStart_183047 : Nat := 118140960795 + 183047 * 2 ^ 59
def prefixEnd_183047 : Nat := 4983230072969 + 3 ^ 40 * 183047 * 2
def baseEnd_183047 : Nat := 83547638545467165751723

theorem tailTrace_183047 : CollatzResearch.WordTrace tailWord_183047 prefixEnd_183047 83547638545467165751723 := by
  unfold tailWord_183047
  simp only [CollatzResearch.WordTrace]
  refine ⟨6676272567859455783819395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4450848378572970522546263 6676272567859455783819395)
  ·
    refine ⟨10014408851789183675729093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6676272567859455783819395 10014408851789183675729093)
    ·
      refine ⟨1877701659710471939199205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10014408851789183675729093 1877701659710471939199205)
      ·
        refine ⟨352069061195713488599851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1877701659710471939199205 352069061195713488599851)
        ·
          refine ⟨528103591793570232899777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352069061195713488599851 528103591793570232899777)
          ·
            refine ⟨396077693845177674674833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528103591793570232899777 396077693845177674674833)
            ·
              refine ⟨297058270383883256006125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396077693845177674674833 297058270383883256006125)
              ·
                refine ⟨111396851393956221002297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297058270383883256006125 111396851393956221002297)
                ·
                  refine ⟨83547638545467165751723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111396851393956221002297 83547638545467165751723)
                  ·
                    rfl

theorem cell20_183047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 2].length) (baseStart_183047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183047 prefixEnd_183047 := by exact prefixLift 183047
  have htrace : WordTrace (prefixWord ++ tailWord_183047) baseStart_183047 baseEnd_183047 := by
    simpa [prefixWord, tailWord_183047, baseEnd_183047] using wordTrace_append hprefix tailTrace_183047
  have hstable : (prefixWord ++ tailWord_183047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183047).length < 2 ^ (prefixWord ++ tailWord_183047).sum := by decide
  have hdescent : baseEnd_183047 < baseStart_183047 := by decide
  rcases family_descends (prefixWord ++ tailWord_183047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183065 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 3]
def baseStart_183065 : Nat := 118140960795 + 183065 * 2 ^ 59
def prefixEnd_183065 : Nat := 4983230072969 + 3 ^ 40 * 183065 * 2
def baseEnd_183065 : Nat := 83555854235939103151649

theorem tailTrace_183065 : CollatzResearch.WordTrace tailWord_183065 prefixEnd_183065 83555854235939103151649 := by
  unfold tailWord_183065
  simp only [CollatzResearch.WordTrace]
  refine ⟨6676929081794244857974649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4451286054529496571983099 6676929081794244857974649)
  ·
    refine ⟨5007696811345683643480987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6676929081794244857974649 5007696811345683643480987)
    ·
      refine ⟨7511545217018525465221481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5007696811345683643480987 7511545217018525465221481)
      ·
        refine ⟨5633658912763894098916111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7511545217018525465221481 5633658912763894098916111)
        ·
          refine ⟨8450488369145841148374167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5633658912763894098916111 8450488369145841148374167)
          ·
            refine ⟨12675732553718761722561251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8450488369145841148374167 12675732553718761722561251)
            ·
              refine ⟨19013598830578142583841877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12675732553718761722561251 19013598830578142583841877)
              ·
                refine ⟨222815611295837608404397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 19013598830578142583841877 222815611295837608404397)
                ·
                  refine ⟨83555854235939103151649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222815611295837608404397 83555854235939103151649)
                  ·
                    rfl

theorem cell20_183065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_183065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183065 prefixEnd_183065 := by exact prefixLift 183065
  have htrace : WordTrace (prefixWord ++ tailWord_183065) baseStart_183065 baseEnd_183065 := by
    simpa [prefixWord, tailWord_183065, baseEnd_183065] using wordTrace_append hprefix tailTrace_183065
  have hstable : (prefixWord ++ tailWord_183065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183065).length < 2 ^ (prefixWord ++ tailWord_183065).sum := by decide
  have hdescent : baseEnd_183065 < baseStart_183065 := by decide
  rcases family_descends (prefixWord ++ tailWord_183065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183068 : List Nat := [2, 2, 3, 1, 1, 3, 2, 4, 2]
def baseStart_183068 : Nat := 118140960795 + 183068 * 2 ^ 59
def prefixEnd_183068 : Nat := 4983230072969 + 3 ^ 40 * 183068 * 2
def baseEnd_183068 : Nat := 83557223517684426051637

theorem tailTrace_183068 : CollatzResearch.WordTrace tailWord_183068 prefixEnd_183068 83557223517684426051637 := by
  unfold tailWord_183068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3338519250391688185166929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4451359000522250913555905 3338519250391688185166929)
  ·
    refine ⟨2503889437793766138875197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3338519250391688185166929 2503889437793766138875197)
    ·
      refine ⟨938958539172662302078199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2503889437793766138875197 938958539172662302078199)
      ·
        refine ⟨1408437808758993453117299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 938958539172662302078199 1408437808758993453117299)
        ·
          refine ⟨2112656713138490179675949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408437808758993453117299 2112656713138490179675949)
          ·
            refine ⟨792246267426933817378481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2112656713138490179675949 792246267426933817378481)
            ·
              refine ⟨594184700570200363033861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792246267426933817378481 594184700570200363033861)
              ·
                refine ⟨111409631356912568068849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 594184700570200363033861 111409631356912568068849)
                ·
                  refine ⟨83557223517684426051637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111409631356912568068849 83557223517684426051637)
                  ·
                    rfl

theorem cell20_183068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_183068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183068 prefixEnd_183068 := by exact prefixLift 183068
  have htrace : WordTrace (prefixWord ++ tailWord_183068) baseStart_183068 baseEnd_183068 := by
    simpa [prefixWord, tailWord_183068, baseEnd_183068] using wordTrace_append hprefix tailTrace_183068
  have hstable : (prefixWord ++ tailWord_183068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183068).length < 2 ^ (prefixWord ++ tailWord_183068).sum := by decide
  have hdescent : baseEnd_183068 < baseStart_183068 := by decide
  rcases family_descends (prefixWord ++ tailWord_183068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183102 : List Nat := [4, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_183102 : Nat := 118140960795 + 183102 * 2 ^ 59
def prefixEnd_183102 : Nat := 4983230072969 + 3 ^ 40 * 183102 * 2
def baseEnd_183102 : Nat := 83572742044131418918165

theorem tailTrace_183102 : CollatzResearch.WordTrace tailWord_183102 prefixEnd_183102 83572742044131418918165 := by
  unfold tailWord_183102
  simp only [CollatzResearch.WordTrace]
  refine ⟨834784822832525022133945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4452185721773466784714373 834784822832525022133945)
  ·
    refine ⟨626088617124393766600459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 834784822832525022133945 626088617124393766600459)
    ·
      refine ⟨939132925686590649900689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626088617124393766600459 939132925686590649900689)
      ·
        refine ⟨704349694264942987425517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 939132925686590649900689 704349694264942987425517)
        ·
          refine ⟨264131135349353620284569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 704349694264942987425517 264131135349353620284569)
          ·
            refine ⟨198098351512015215213427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264131135349353620284569 198098351512015215213427)
            ·
              refine ⟨297147527268022822820141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198098351512015215213427 297147527268022822820141)
              ·
                refine ⟨111430322725508558557553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297147527268022822820141 111430322725508558557553)
                ·
                  refine ⟨83572742044131418918165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111430322725508558557553 83572742044131418918165)
                  ·
                    rfl

theorem cell20_183102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_183102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183102 prefixEnd_183102 := by exact prefixLift 183102
  have htrace : WordTrace (prefixWord ++ tailWord_183102) baseStart_183102 baseEnd_183102 := by
    simpa [prefixWord, tailWord_183102, baseEnd_183102] using wordTrace_append hprefix tailTrace_183102
  have hstable : (prefixWord ++ tailWord_183102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183102).length < 2 ^ (prefixWord ++ tailWord_183102).sum := by decide
  have hdescent : baseEnd_183102 < baseStart_183102 := by decide
  rcases family_descends (prefixWord ++ tailWord_183102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183103 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 5]
def baseStart_183103 : Nat := 118140960795 + 183103 * 2 ^ 59
def prefixEnd_183103 : Nat := 4983230072969 + 3 ^ 40 * 183103 * 2
def baseEnd_183103 : Nat := 83573198471379859884827

theorem tailTrace_183103 : CollatzResearch.WordTrace tailWord_183103 prefixEnd_183103 83573198471379859884827 := by
  unfold tailWord_183103
  simp only [CollatzResearch.WordTrace]
  refine ⟨6678315055656577347857963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4452210037104384898571975 6678315055656577347857963)
  ·
    refine ⟨10017472583484866021786945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6678315055656577347857963 10017472583484866021786945)
    ·
      refine ⟨7513104437613649516340209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10017472583484866021786945 7513104437613649516340209)
      ·
        refine ⟨5634828328210237137255157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7513104437613649516340209 5634828328210237137255157)
        ·
          refine ⟨528265155769709731617671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5634828328210237137255157 528265155769709731617671)
          ·
            refine ⟨792397733654564597426507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528265155769709731617671 792397733654564597426507)
            ·
              refine ⟨1188596600481846896139761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792397733654564597426507 1188596600481846896139761)
              ·
                refine ⟨891447450361385172104821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1188596600481846896139761 891447450361385172104821)
                ·
                  refine ⟨83573198471379859884827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 891447450361385172104821 83573198471379859884827)
                  ·
                    rfl

theorem cell20_183103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_183103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183103 prefixEnd_183103 := by exact prefixLift 183103
  have htrace : WordTrace (prefixWord ++ tailWord_183103) baseStart_183103 baseEnd_183103 := by
    simpa [prefixWord, tailWord_183103, baseEnd_183103] using wordTrace_append hprefix tailTrace_183103
  have hstable : (prefixWord ++ tailWord_183103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183103).length < 2 ^ (prefixWord ++ tailWord_183103).sum := by decide
  have hdescent : baseEnd_183103 < baseStart_183103 := by decide
  rcases family_descends (prefixWord ++ tailWord_183103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183127 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 4]
def baseStart_183127 : Nat := 118140960795 + 183127 * 2 ^ 59
def prefixEnd_183127 : Nat := 4983230072969 + 3 ^ 40 * 183127 * 2
def baseEnd_183127 : Nat := 83584152725342443084729

theorem tailTrace_183127 : CollatzResearch.WordTrace tailWord_183127 prefixEnd_183127 83584152725342443084729 := by
  unfold tailWord_183127
  simp only [CollatzResearch.WordTrace]
  refine ⟨6679190407569629446731635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4452793605046419631154423 6679190407569629446731635)
  ·
    refine ⟨10018785611354444170097453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6679190407569629446731635 10018785611354444170097453)
    ·
      refine ⟨3757044604257916563786545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10018785611354444170097453 3757044604257916563786545)
      ·
        refine ⟨2817783453193437422839909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3757044604257916563786545 2817783453193437422839909)
        ·
          refine ⟨528334397473769516782483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2817783453193437422839909 528334397473769516782483)
          ·
            refine ⟨792501596210654275173725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528334397473769516782483 792501596210654275173725)
            ·
              refine ⟨297188098578995353190147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 792501596210654275173725 297188098578995353190147)
              ·
                refine ⟨445782147868493029785221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297188098578995353190147 445782147868493029785221)
                ·
                  refine ⟨83584152725342443084729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 445782147868493029785221 83584152725342443084729)
                  ·
                    rfl

theorem cell20_183127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_183127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183127 prefixEnd_183127 := by exact prefixLift 183127
  have htrace : WordTrace (prefixWord ++ tailWord_183127) baseStart_183127 baseEnd_183127 := by
    simpa [prefixWord, tailWord_183127, baseEnd_183127] using wordTrace_append hprefix tailTrace_183127
  have hstable : (prefixWord ++ tailWord_183127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183127).length < 2 ^ (prefixWord ++ tailWord_183127).sum := by decide
  have hdescent : baseEnd_183127 < baseStart_183127 := by decide
  rcases family_descends (prefixWord ++ tailWord_183127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183148 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_183148 : Nat := 118140960795 + 183148 * 2 ^ 59
def prefixEnd_183148 : Nat := 4983230072969 + 3 ^ 40 * 183148 * 2
def baseEnd_183148 : Nat := 83593737697559703384643

theorem tailTrace_183148 : CollatzResearch.WordTrace tailWord_183148 prefixEnd_183148 83593737697559703384643 := by
  unfold tailWord_183148
  simp only [CollatzResearch.WordTrace]
  refine ⟨3339978170246775016623049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4453304226995700022164065 3339978170246775016623049)
  ·
    refine ⟨2504983627685081262467287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3339978170246775016623049 2504983627685081262467287)
    ·
      refine ⟨3757475441527621893700931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2504983627685081262467287 3757475441527621893700931)
      ·
        refine ⟨5636213162291432840551397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3757475441527621893700931 5636213162291432840551397)
        ·
          refine ⟨1056789967929643657603387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5636213162291432840551397 1056789967929643657603387)
          ·
            refine ⟨1585184951894465486405081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056789967929643657603387 1585184951894465486405081)
            ·
              refine ⟨1188888713920849114803811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1585184951894465486405081 1188888713920849114803811)
              ·
                refine ⟨1783333070881273672205717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188888713920849114803811 1783333070881273672205717)
                ·
                  refine ⟨83593737697559703384643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1783333070881273672205717 83593737697559703384643)
                  ·
                    rfl

theorem cell20_183148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_183148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183148 prefixEnd_183148 := by exact prefixLift 183148
  have htrace : WordTrace (prefixWord ++ tailWord_183148) baseStart_183148 baseEnd_183148 := by
    simpa [prefixWord, tailWord_183148, baseEnd_183148] using wordTrace_append hprefix tailTrace_183148
  have hstable : (prefixWord ++ tailWord_183148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183148).length < 2 ^ (prefixWord ++ tailWord_183148).sum := by decide
  have hdescent : baseEnd_183148 < baseStart_183148 := by decide
  rcases family_descends (prefixWord ++ tailWord_183148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183155 : List Nat := [1, 1, 1, 2, 2, 1, 6, 6]
def baseStart_183155 : Nat := 118140960795 + 183155 * 2 ^ 59
def prefixEnd_183155 : Nat := 4983230072969 + 3 ^ 40 * 183155 * 2
def baseEnd_183155 : Nat := 27865644229432930050427

theorem tailTrace_183155 : CollatzResearch.WordTrace tailWord_183155 prefixEnd_183155 27865644229432930050427 := by
  unfold tailWord_183155
  simp only [CollatzResearch.WordTrace]
  refine ⟨6680211651468190228750919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4453474434312126819167279 6680211651468190228750919)
  ·
    refine ⟨10020317477202285343126379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6680211651468190228750919 10020317477202285343126379)
    ·
      refine ⟨15030476215803428014689569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10020317477202285343126379 15030476215803428014689569)
      ·
        refine ⟨11272857161852571011017177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15030476215803428014689569 11272857161852571011017177)
        ·
          refine ⟨8454642871389428258262883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11272857161852571011017177 8454642871389428258262883)
          ·
            refine ⟨12681964307084142387394325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8454642871389428258262883 12681964307084142387394325)
            ·
              refine ⟨594467076894569174409109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12681964307084142387394325 594467076894569174409109)
              ·
                refine ⟨27865644229432930050427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 594467076894569174409109 27865644229432930050427)
                ·
                  rfl

theorem cell20_183155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_183155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183155 prefixEnd_183155 := by exact prefixLift 183155
  have htrace : WordTrace (prefixWord ++ tailWord_183155) baseStart_183155 baseEnd_183155 := by
    simpa [prefixWord, tailWord_183155, baseEnd_183155] using wordTrace_append hprefix tailTrace_183155
  have hstable : (prefixWord ++ tailWord_183155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183155).length < 2 ^ (prefixWord ++ tailWord_183155).sum := by decide
  have hdescent : baseEnd_183155 < baseStart_183155 := by decide
  rcases family_descends (prefixWord ++ tailWord_183155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183178 : List Nat := [3, 1, 2, 4, 1, 3, 2, 2, 2]
def baseStart_183178 : Nat := 118140960795 + 183178 * 2 ^ 59
def prefixEnd_183178 : Nat := 4983230072969 + 3 ^ 40 * 183178 * 2
def baseEnd_183178 : Nat := 83607430515012932384521

theorem tailTrace_183178 : CollatzResearch.WordTrace tailWord_183178 prefixEnd_183178 83607430515012932384521 := by
  unfold tailWord_183178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670262632596216289209547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4454033686923243437892125 1670262632596216289209547)
  ·
    refine ⟨2505393948894324433814321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1670262632596216289209547 2505393948894324433814321)
    ·
      refine ⟨1879045461670743325360741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2505393948894324433814321 1879045461670743325360741)
      ·
        refine ⟨352321024063264373505139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1879045461670743325360741 352321024063264373505139)
        ·
          refine ⟨528481536094896560257709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352321024063264373505139 528481536094896560257709)
          ·
            refine ⟨198180576035586210096641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 528481536094896560257709 198180576035586210096641)
            ·
              refine ⟨148635432026689657572481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198180576035586210096641 148635432026689657572481)
              ·
                refine ⟨111476574020017243179361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148635432026689657572481 111476574020017243179361)
                ·
                  refine ⟨83607430515012932384521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111476574020017243179361 83607430515012932384521)
                  ·
                    rfl

theorem cell20_183178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_183178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183178 prefixEnd_183178 := by exact prefixLift 183178
  have htrace : WordTrace (prefixWord ++ tailWord_183178) baseStart_183178 baseEnd_183178 := by
    simpa [prefixWord, tailWord_183178, baseEnd_183178] using wordTrace_append hprefix tailTrace_183178
  have hstable : (prefixWord ++ tailWord_183178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183178).length < 2 ^ (prefixWord ++ tailWord_183178).sum := by decide
  have hdescent : baseEnd_183178 < baseStart_183178 := by decide
  rcases family_descends (prefixWord ++ tailWord_183178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183179 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 3]
def baseStart_183179 : Nat := 118140960795 + 183179 * 2 ^ 59
def prefixEnd_183179 : Nat := 4983230072969 + 3 ^ 40 * 183179 * 2
def baseEnd_183179 : Nat := 83607886942261373351183

theorem tailTrace_183179 : CollatzResearch.WordTrace tailWord_183179 prefixEnd_183179 83607886942261373351183 := by
  unfold tailWord_183179
  simp only [CollatzResearch.WordTrace]
  refine ⟨6681087003381242327624591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4454058002254161551749727 6681087003381242327624591)
  ·
    refine ⟨10021630505071863491436887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6681087003381242327624591 10021630505071863491436887)
    ·
      refine ⟨15032445757607795237155331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10021630505071863491436887 15032445757607795237155331)
      ·
        refine ⟨22548668636411692855732997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15032445757607795237155331 22548668636411692855732997)
        ·
          refine ⟨4227875369327192410449937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22548668636411692855732997 4227875369327192410449937)
          ·
            refine ⟨3170906526995394307837453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4227875369327192410449937 3170906526995394307837453)
            ·
              refine ⟨1189089947623272865439045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3170906526995394307837453 1189089947623272865439045)
              ·
                refine ⟨222954365179363662269821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1189089947623272865439045 222954365179363662269821)
                ·
                  refine ⟨83607886942261373351183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222954365179363662269821 83607886942261373351183)
                  ·
                    rfl

theorem cell20_183179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 3].length) (baseStart_183179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183179 prefixEnd_183179 := by exact prefixLift 183179
  have htrace : WordTrace (prefixWord ++ tailWord_183179) baseStart_183179 baseEnd_183179 := by
    simpa [prefixWord, tailWord_183179, baseEnd_183179] using wordTrace_append hprefix tailTrace_183179
  have hstable : (prefixWord ++ tailWord_183179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183179).length < 2 ^ (prefixWord ++ tailWord_183179).sum := by decide
  have hdescent : baseEnd_183179 < baseStart_183179 := by decide
  rcases family_descends (prefixWord ++ tailWord_183179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183282 : List Nat := [3, 2, 1, 5, 2, 1, 6]
def baseStart_183282 : Nat := 118140960795 + 183282 * 2 ^ 59
def prefixEnd_183282 : Nat := 4983230072969 + 3 ^ 40 * 183282 * 2
def baseEnd_183282 : Nat := 9294988772094532546381

theorem tailTrace_183282 : CollatzResearch.WordTrace tailWord_183282 prefixEnd_183282 9294988772094532546381 := by
  unfold tailWord_183282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671210930502022729656025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4456562481338727279082733 1671210930502022729656025)
  ·
    refine ⟨1253408197876517047242019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1671210930502022729656025 1253408197876517047242019)
    ·
      refine ⟨1880112296814775570863029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253408197876517047242019 1880112296814775570863029)
      ·
        refine ⟨176260527826385209768409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1880112296814775570863029 176260527826385209768409)
        ·
          refine ⟨132195395869788907326307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176260527826385209768409 132195395869788907326307)
          ·
            refine ⟨198293093804683360989461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132195395869788907326307 198293093804683360989461)
            ·
              refine ⟨9294988772094532546381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198293093804683360989461 9294988772094532546381)
              ·
                rfl

theorem cell20_183282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 6].length) (baseStart_183282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183282 prefixEnd_183282 := by exact prefixLift 183282
  have htrace : WordTrace (prefixWord ++ tailWord_183282) baseStart_183282 baseEnd_183282 := by
    simpa [prefixWord, tailWord_183282, baseEnd_183282] using wordTrace_append hprefix tailTrace_183282
  have hstable : (prefixWord ++ tailWord_183282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183282).length < 2 ^ (prefixWord ++ tailWord_183282).sum := by decide
  have hdescent : baseEnd_183282 < baseStart_183282 := by decide
  rcases family_descends (prefixWord ++ tailWord_183282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183286 : List Nat := [5, 1, 1, 1, 3, 1, 8]
def baseStart_183286 : Nat := 118140960795 + 183286 * 2 ^ 59
def prefixEnd_183286 : Nat := 4983230072969 + 3 ^ 40 * 183286 * 2
def baseEnd_183286 : Nat := 9295191628649395198231

theorem tailTrace_183286 : CollatzResearch.WordTrace tailWord_183286 prefixEnd_183286 9295191628649395198231 := by
  unfold tailWord_183286
  simp only [CollatzResearch.WordTrace]
  refine ⟨417811850874599975110607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4456659742662399734513141 417811850874599975110607)
  ·
    refine ⟨626717776311899962665911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 417811850874599975110607 626717776311899962665911)
    ·
      refine ⟨940076664467849943998867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626717776311899962665911 940076664467849943998867)
      ·
        refine ⟨1410114996701774915998301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940076664467849943998867 1410114996701774915998301)
        ·
          refine ⟨528793123763165593499363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1410114996701774915998301 528793123763165593499363)
          ·
            refine ⟨793189685644748390249045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528793123763165593499363 793189685644748390249045)
            ·
              refine ⟨9295191628649395198231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 793189685644748390249045 9295191628649395198231)
              ·
                rfl

theorem cell20_183286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 8].length) (baseStart_183286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183286 prefixEnd_183286 := by exact prefixLift 183286
  have htrace : WordTrace (prefixWord ++ tailWord_183286) baseStart_183286 baseEnd_183286 := by
    simpa [prefixWord, tailWord_183286, baseEnd_183286] using wordTrace_append hprefix tailTrace_183286
  have hstable : (prefixWord ++ tailWord_183286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183286).length < 2 ^ (prefixWord ++ tailWord_183286).sum := by decide
  have hdescent : baseEnd_183286 < baseStart_183286 := by decide
  rcases family_descends (prefixWord ++ tailWord_183286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183293 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 3]
def baseStart_183293 : Nat := 118140960795 + 183293 * 2 ^ 59
def prefixEnd_183293 : Nat := 4983230072969 + 3 ^ 40 * 183293 * 2
def baseEnd_183293 : Nat := 83659919648583643550717

theorem tailTrace_183293 : CollatzResearch.WordTrace tailWord_183293 prefixEnd_183293 83659919648583643550717 := by
  unfold tailWord_183293
  simp only [CollatzResearch.WordTrace]
  refine ⟨6685244924968239797274533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4456829949978826531516355 6685244924968239797274533)
  ·
    refine ⟨1253483423431544961988975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6685244924968239797274533 1253483423431544961988975)
    ·
      refine ⟨1880225135147317442983463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253483423431544961988975 1880225135147317442983463)
      ·
        refine ⟨2820337702720976164475195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880225135147317442983463 2820337702720976164475195)
        ·
          refine ⟨4230506554081464246712793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820337702720976164475195 4230506554081464246712793)
          ·
            refine ⟨3172879915561098185034595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4230506554081464246712793 3172879915561098185034595)
            ·
              refine ⟨4759319873341647277551893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3172879915561098185034595 4759319873341647277551893)
              ·
                refine ⟨223093119062889716135245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4759319873341647277551893 223093119062889716135245)
                ·
                  refine ⟨83659919648583643550717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223093119062889716135245 83659919648583643550717)
                  ·
                    rfl

theorem cell20_183293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_183293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183293 prefixEnd_183293 := by exact prefixLift 183293
  have htrace : WordTrace (prefixWord ++ tailWord_183293) baseStart_183293 baseEnd_183293 := by
    simpa [prefixWord, tailWord_183293, baseEnd_183293] using wordTrace_append hprefix tailTrace_183293
  have hstable : (prefixWord ++ tailWord_183293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183293).length < 2 ^ (prefixWord ++ tailWord_183293).sum := by decide
  have hdescent : baseEnd_183293 < baseStart_183293 := by decide
  rcases family_descends (prefixWord ++ tailWord_183293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183307 : List Nat := [1, 1, 1, 1, 6, 2, 1, 7]
def baseStart_183307 : Nat := 118140960795 + 183307 * 2 ^ 59
def prefixEnd_183307 : Nat := 4983230072969 + 3 ^ 40 * 183307 * 2
def baseEnd_183307 : Nat := 27888769876687272361331

theorem tailTrace_183307 : CollatzResearch.WordTrace tailWord_183307 prefixEnd_183307 27888769876687272361331 := by
  unfold tailWord_183307
  simp only [CollatzResearch.WordTrace]
  refine ⟨6685755546917520188284175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4457170364611680125522783 6685755546917520188284175)
  ·
    refine ⟨10028633320376280282426263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6685755546917520188284175 10028633320376280282426263)
    ·
      refine ⟨15042949980564420423639395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10028633320376280282426263 15042949980564420423639395)
      ·
        refine ⟨22564424970846630635459093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15042949980564420423639395 22564424970846630635459093)
        ·
          refine ⟨1057707420508435811037145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22564424970846630635459093 1057707420508435811037145)
          ·
            refine ⟨793280565381326858277859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057707420508435811037145 793280565381326858277859)
            ·
              refine ⟨1189920848071990287416789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793280565381326858277859 1189920848071990287416789)
              ·
                refine ⟨27888769876687272361331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1189920848071990287416789 27888769876687272361331)
                ·
                  rfl

theorem cell20_183307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_183307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183307 prefixEnd_183307 := by exact prefixLift 183307
  have htrace : WordTrace (prefixWord ++ tailWord_183307) baseStart_183307 baseEnd_183307 := by
    simpa [prefixWord, tailWord_183307, baseEnd_183307] using wordTrace_append hprefix tailTrace_183307
  have hstable : (prefixWord ++ tailWord_183307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183307).length < 2 ^ (prefixWord ++ tailWord_183307).sum := by decide
  have hdescent : baseEnd_183307 < baseStart_183307 := by decide
  rcases family_descends (prefixWord ++ tailWord_183307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183310 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_183310 : Nat := 118140960795 + 183310 * 2 ^ 59
def prefixEnd_183310 : Nat := 4983230072969 + 3 ^ 40 * 183310 * 2
def baseEnd_183310 : Nat := 83667678911807139983981

theorem tailTrace_183310 : CollatzResearch.WordTrace tailWord_183310 prefixEnd_183310 83667678911807139983981 := by
  unfold tailWord_183310
  simp only [CollatzResearch.WordTrace]
  refine ⟨835733120738331462580423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4457243310604434467095589 835733120738331462580423)
  ·
    refine ⟨1253599681107497193870635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 835733120738331462580423 1253599681107497193870635)
    ·
      refine ⟨1880399521661245790805953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253599681107497193870635 1880399521661245790805953)
      ·
        refine ⟨1410299641245934343104465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1880399521661245790805953 1410299641245934343104465)
        ·
          refine ⟨1057724730934450757328349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1410299641245934343104465 1057724730934450757328349)
          ·
            refine ⟨396646774100419033998131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1057724730934450757328349 396646774100419033998131)
            ·
              refine ⟨594970161150628550997197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396646774100419033998131 594970161150628550997197)
              ·
                refine ⟨223113810431485706623949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 594970161150628550997197 223113810431485706623949)
                ·
                  refine ⟨83667678911807139983981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223113810431485706623949 83667678911807139983981)
                  ·
                    rfl

theorem cell20_183310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_183310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183310 prefixEnd_183310 := by exact prefixLift 183310
  have htrace : WordTrace (prefixWord ++ tailWord_183310) baseStart_183310 baseEnd_183310 := by
    simpa [prefixWord, tailWord_183310, baseEnd_183310] using wordTrace_append hprefix tailTrace_183310
  have hstable : (prefixWord ++ tailWord_183310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183310).length < 2 ^ (prefixWord ++ tailWord_183310).sum := by decide
  have hdescent : baseEnd_183310 < baseStart_183310 := by decide
  rcases family_descends (prefixWord ++ tailWord_183310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183393 : List Nat := [1, 2, 3, 1, 1, 2, 3, 5, 2]
def baseStart_183393 : Nat := 118140960795 + 183393 * 2 ^ 59
def prefixEnd_183393 : Nat := 4983230072969 + 3 ^ 40 * 183393 * 2
def baseEnd_183393 : Nat := 83705562373427740216975

theorem tailTrace_183393 : CollatzResearch.WordTrace tailWord_183393 prefixEnd_183393 83705562373427740216975 := by
  unfold tailWord_183393
  simp only [CollatzResearch.WordTrace]
  refine ⟨6688892224605956875914833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4459261483070637917276555 6688892224605956875914833)
  ·
    refine ⟨5016669168454467656936125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6688892224605956875914833 5016669168454467656936125)
    ·
      refine ⟨1881250938170425371351047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5016669168454467656936125 1881250938170425371351047)
      ·
        refine ⟨2821876407255638057026571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881250938170425371351047 2821876407255638057026571)
        ·
          refine ⟨4232814610883457085539857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2821876407255638057026571 4232814610883457085539857)
          ·
            refine ⟨3174610958162592814154893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4232814610883457085539857 3174610958162592814154893)
            ·
              refine ⟨1190479109310972305308085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3174610958162592814154893 1190479109310972305308085)
              ·
                refine ⟨111607416497903653622633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1190479109310972305308085 111607416497903653622633)
                ·
                  refine ⟨83705562373427740216975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111607416497903653622633 83705562373427740216975)
                  ·
                    rfl

theorem cell20_183393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 2].length) (baseStart_183393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183393 prefixEnd_183393 := by exact prefixLift 183393
  have htrace : WordTrace (prefixWord ++ tailWord_183393) baseStart_183393 baseEnd_183393 := by
    simpa [prefixWord, tailWord_183393, baseEnd_183393] using wordTrace_append hprefix tailTrace_183393
  have hstable : (prefixWord ++ tailWord_183393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183393).length < 2 ^ (prefixWord ++ tailWord_183393).sum := by decide
  have hdescent : baseEnd_183393 < baseStart_183393 := by decide
  rcases family_descends (prefixWord ++ tailWord_183393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183421 : List Nat := [1, 4, 1, 1, 3, 1, 2, 7]
def baseStart_183421 : Nat := 118140960795 + 183421 * 2 ^ 59
def prefixEnd_183421 : Nat := 4983230072969 + 3 ^ 40 * 183421 * 2
def baseEnd_183421 : Nat := 27906114112128029094509

theorem tailTrace_183421 : CollatzResearch.WordTrace tailWord_183421 prefixEnd_183421 27906114112128029094509 := by
  unfold tailWord_183421
  simp only [CollatzResearch.WordTrace]
  refine ⟨6689913468504517657934117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4459942312336345105289411 6689913468504517657934117)
  ·
    refine ⟨1254358775344597060862647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6689913468504517657934117 1254358775344597060862647)
    ·
      refine ⟨1881538163016895591293971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1254358775344597060862647 1881538163016895591293971)
      ·
        refine ⟨2822307244525343386940957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881538163016895591293971 2822307244525343386940957)
        ·
          refine ⟨1058365216697003770102859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2822307244525343386940957 1058365216697003770102859)
          ·
            refine ⟨1587547825045505655154289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058365216697003770102859 1587547825045505655154289)
            ·
              refine ⟨1190660868784129241365717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587547825045505655154289 1190660868784129241365717)
              ·
                refine ⟨27906114112128029094509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1190660868784129241365717 27906114112128029094509)
                ·
                  rfl

theorem cell20_183421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_183421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183421 prefixEnd_183421 := by exact prefixLift 183421
  have htrace : WordTrace (prefixWord ++ tailWord_183421) baseStart_183421 baseEnd_183421 := by
    simpa [prefixWord, tailWord_183421, baseEnd_183421] using wordTrace_append hprefix tailTrace_183421
  have hstable : (prefixWord ++ tailWord_183421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183421).length < 2 ^ (prefixWord ++ tailWord_183421).sum := by decide
  have hdescent : baseEnd_183421 < baseStart_183421 := by decide
  rcases family_descends (prefixWord ++ tailWord_183421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183438 : List Nat := [4, 1, 1, 3, 2, 2, 1, 6]
def baseStart_183438 : Nat := 118140960795 + 183438 * 2 ^ 59
def prefixEnd_183438 : Nat := 4983230072969 + 3 ^ 40 * 183438 * 2
def baseEnd_183438 : Nat := 27908700533202527905597

theorem tailTrace_183438 : CollatzResearch.WordTrace tailWord_183438 prefixEnd_183438 27908700533202527905597 := by
  unfold tailWord_183438
  simp only [CollatzResearch.WordTrace]
  refine ⟨836316688680366195162871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4460355672961953040868645 836316688680366195162871)
  ·
    refine ⟨1254475033020549292744307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 836316688680366195162871 1254475033020549292744307)
    ·
      refine ⟨1881712549530823939116461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1254475033020549292744307 1881712549530823939116461)
      ·
        refine ⟨705642206074058977168673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1881712549530823939116461 705642206074058977168673)
        ·
          refine ⟨529231654555544232876505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705642206074058977168673 529231654555544232876505)
          ·
            refine ⟨396923740916658174657379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529231654555544232876505 396923740916658174657379)
            ·
              refine ⟨595385611374987261986069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396923740916658174657379 595385611374987261986069)
              ·
                refine ⟨27908700533202527905597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 595385611374987261986069 27908700533202527905597)
                ·
                  rfl

theorem cell20_183438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_183438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183438 prefixEnd_183438 := by exact prefixLift 183438
  have htrace : WordTrace (prefixWord ++ tailWord_183438) baseStart_183438 baseEnd_183438 := by
    simpa [prefixWord, tailWord_183438, baseEnd_183438] using wordTrace_append hprefix tailTrace_183438
  have hstable : (prefixWord ++ tailWord_183438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183438).length < 2 ^ (prefixWord ++ tailWord_183438).sum := by decide
  have hdescent : baseEnd_183438 < baseStart_183438 := by decide
  rcases family_descends (prefixWord ++ tailWord_183438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183448 : List Nat := [2, 1, 2, 4, 2, 1, 3, 3, 2]
def baseStart_183448 : Nat := 118140960795 + 183448 * 2 ^ 59
def prefixEnd_183448 : Nat := 4983230072969 + 3 ^ 40 * 183448 * 2
def baseEnd_183448 : Nat := 83730665872091993383417

theorem tailTrace_183448 : CollatzResearch.WordTrace tailWord_183448 prefixEnd_183448 83730665872091993383417 := by
  unfold tailWord_183448
  simp only [CollatzResearch.WordTrace]
  refine ⟨3345449119703350634583499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4460598826271134179444665 3345449119703350634583499)
  ·
    refine ⟨5018173679555025951875249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3345449119703350634583499 5018173679555025951875249)
    ·
      refine ⟨3763630259666269463906437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5018173679555025951875249 3763630259666269463906437)
      ·
        refine ⟨705680673687425524482457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3763630259666269463906437 705680673687425524482457)
        ·
          refine ⟨529260505265569143361843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705680673687425524482457 529260505265569143361843)
          ·
            refine ⟨793890757898353715042765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529260505265569143361843 793890757898353715042765)
            ·
              refine ⟨297709034211882643141037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 793890757898353715042765 297709034211882643141037)
              ·
                refine ⟨111640887829455991177889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297709034211882643141037 111640887829455991177889)
                ·
                  refine ⟨83730665872091993383417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111640887829455991177889 83730665872091993383417)
                  ·
                    rfl

theorem cell20_183448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 2].length) (baseStart_183448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183448 prefixEnd_183448 := by exact prefixLift 183448
  have htrace : WordTrace (prefixWord ++ tailWord_183448) baseStart_183448 baseEnd_183448 := by
    simpa [prefixWord, tailWord_183448, baseEnd_183448] using wordTrace_append hprefix tailTrace_183448
  have hstable : (prefixWord ++ tailWord_183448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183448).length < 2 ^ (prefixWord ++ tailWord_183448).sum := by decide
  have hdescent : baseEnd_183448 < baseStart_183448 := by decide
  rcases family_descends (prefixWord ++ tailWord_183448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183455 : List Nat := [1, 1, 2, 6, 3, 1, 6]
def baseStart_183455 : Nat := 118140960795 + 183455 * 2 ^ 59
def prefixEnd_183455 : Nat := 4983230072969 + 3 ^ 40 * 183455 * 2
def baseEnd_183455 : Nat := 9303762318092342238895

theorem tailTrace_183455 : CollatzResearch.WordTrace tailWord_183455 prefixEnd_183455 9303762318092342238895 := by
  unfold tailWord_183455
  simp only [CollatzResearch.WordTrace]
  refine ⟨6691153550381341464671819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4460769033587560976447879 6691153550381341464671819)
  ·
    refine ⟨10036730325572012197007729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6691153550381341464671819 10036730325572012197007729)
    ·
      refine ⟨7527547744179009147755797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10036730325572012197007729 7527547744179009147755797)
      ·
        refine ⟨352853800508391053801053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7527547744179009147755797 352853800508391053801053)
        ·
          refine ⟨132320175190646645175395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352853800508391053801053 132320175190646645175395)
          ·
            refine ⟨198480262785969967763093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132320175190646645175395 198480262785969967763093)
            ·
              refine ⟨9303762318092342238895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198480262785969967763093 9303762318092342238895)
              ·
                rfl

theorem cell20_183455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 6].length) (baseStart_183455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183455 prefixEnd_183455 := by exact prefixLift 183455
  have htrace : WordTrace (prefixWord ++ tailWord_183455) baseStart_183455 baseEnd_183455 := by
    simpa [prefixWord, tailWord_183455, baseEnd_183455] using wordTrace_append hprefix tailTrace_183455
  have hstable : (prefixWord ++ tailWord_183455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183455).length < 2 ^ (prefixWord ++ tailWord_183455).sum := by decide
  have hdescent : baseEnd_183455 < baseStart_183455 := by decide
  rcases family_descends (prefixWord ++ tailWord_183455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183517 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 3]
def baseStart_183517 : Nat := 118140960795 + 183517 * 2 ^ 59
def prefixEnd_183517 : Nat := 4983230072969 + 3 ^ 40 * 183517 * 2
def baseEnd_183517 : Nat := 83762159352234420083135

theorem tailTrace_183517 : CollatzResearch.WordTrace tailWord_183517 prefixEnd_183517 83762159352234420083135 := by
  unfold tailWord_183517
  simp only [CollatzResearch.WordTrace]
  refine ⟨6693414876156726053428805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4462276584104484035619203 6693414876156726053428805)
  ·
    refine ⟨1255015289279386135017901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6693414876156726053428805 1255015289279386135017901)
    ·
      refine ⟨470630733479769800631713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1255015289279386135017901 470630733479769800631713)
      ·
        refine ⟨352973050109827350473785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470630733479769800631713 352973050109827350473785)
        ·
          refine ⟨264729787582370512855339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352973050109827350473785 264729787582370512855339)
          ·
            refine ⟨397094681373555769283009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264729787582370512855339 397094681373555769283009)
            ·
              refine ⟨297821011030166826962257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397094681373555769283009 297821011030166826962257)
              ·
                refine ⟨223365758272625120221693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297821011030166826962257 223365758272625120221693)
                ·
                  refine ⟨83762159352234420083135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223365758272625120221693 83762159352234420083135)
                  ·
                    rfl

theorem cell20_183517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_183517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183517 prefixEnd_183517 := by exact prefixLift 183517
  have htrace : WordTrace (prefixWord ++ tailWord_183517) baseStart_183517 baseEnd_183517 := by
    simpa [prefixWord, tailWord_183517, baseEnd_183517] using wordTrace_append hprefix tailTrace_183517
  have hstable : (prefixWord ++ tailWord_183517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183517).length < 2 ^ (prefixWord ++ tailWord_183517).sum := by decide
  have hdescent : baseEnd_183517 < baseStart_183517 := by decide
  rcases family_descends (prefixWord ++ tailWord_183517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183521 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 3]
def baseStart_183521 : Nat := 118140960795 + 183521 * 2 ^ 59
def prefixEnd_183521 : Nat := 4983230072969 + 3 ^ 40 * 183521 * 2
def baseEnd_183521 : Nat := 83763985061228183949785

theorem tailTrace_183521 : CollatzResearch.WordTrace tailWord_183521 prefixEnd_183521 83763985061228183949785 := by
  unfold tailWord_183521
  simp only [CollatzResearch.WordTrace]
  refine ⟨6693560768142234736574417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4462373845428156491049611 6693560768142234736574417)
  ·
    refine ⟨5020170576106676052430813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6693560768142234736574417 5020170576106676052430813)
    ·
      refine ⟨1882563966040003519661555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5020170576106676052430813 1882563966040003519661555)
      ·
        refine ⟨2823845949060005279492333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882563966040003519661555 2823845949060005279492333)
        ·
          refine ⟨1058942230897501979809625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2823845949060005279492333 1058942230897501979809625)
          ·
            refine ⟨794206673173126484857219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1058942230897501979809625 794206673173126484857219)
            ·
              refine ⟨1191310009759689727285829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794206673173126484857219 1191310009759689727285829)
              ·
                refine ⟨223370626829941823866093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1191310009759689727285829 223370626829941823866093)
                ·
                  refine ⟨83763985061228183949785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223370626829941823866093 83763985061228183949785)
                  ·
                    rfl

theorem cell20_183521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_183521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183521 prefixEnd_183521 := by exact prefixLift 183521
  have htrace : WordTrace (prefixWord ++ tailWord_183521) baseStart_183521 baseEnd_183521 := by
    simpa [prefixWord, tailWord_183521, baseEnd_183521] using wordTrace_append hprefix tailTrace_183521
  have hstable : (prefixWord ++ tailWord_183521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183521).length < 2 ^ (prefixWord ++ tailWord_183521).sum := by decide
  have hdescent : baseEnd_183521 < baseStart_183521 := by decide
  rcases family_descends (prefixWord ++ tailWord_183521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183524 : List Nat := [2, 3, 1, 1, 1, 2, 6, 2, 2]
def baseStart_183524 : Nat := 118140960795 + 183524 * 2 ^ 59
def prefixEnd_183524 : Nat := 4983230072969 + 3 ^ 40 * 183524 * 2
def baseEnd_183524 : Nat := 83765354342973506849773

theorem tailTrace_183524 : CollatzResearch.WordTrace tailWord_183524 prefixEnd_183524 83765354342973506849773 := by
  unfold tailWord_183524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346835093565683124466813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4462446791420910832622417 3346835093565683124466813)
  ·
    refine ⟨1255063160087131171675055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3346835093565683124466813 1255063160087131171675055)
    ·
      refine ⟨1882594740130696757512583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1255063160087131171675055 1882594740130696757512583)
      ·
        refine ⟨2823892110196045136268875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882594740130696757512583 2823892110196045136268875)
        ·
          refine ⟨4235838165294067704403313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2823892110196045136268875 4235838165294067704403313)
          ·
            refine ⟨3176878623970550778302485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4235838165294067704403313 3176878623970550778302485)
            ·
              refine ⟨148916185498619567732929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3176878623970550778302485 148916185498619567732929)
              ·
                refine ⟨111687139123964675799697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148916185498619567732929 111687139123964675799697)
                ·
                  refine ⟨83765354342973506849773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111687139123964675799697 83765354342973506849773)
                  ·
                    rfl

theorem cell20_183524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_183524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183524 prefixEnd_183524 := by exact prefixLift 183524
  have htrace : WordTrace (prefixWord ++ tailWord_183524) baseStart_183524 baseEnd_183524 := by
    simpa [prefixWord, tailWord_183524, baseEnd_183524] using wordTrace_append hprefix tailTrace_183524
  have hstable : (prefixWord ++ tailWord_183524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183524).length < 2 ^ (prefixWord ++ tailWord_183524).sum := by decide
  have hdescent : baseEnd_183524 < baseStart_183524 := by decide
  rcases family_descends (prefixWord ++ tailWord_183524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183528 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_183528 : Nat := 118140960795 + 183528 * 2 ^ 59
def prefixEnd_183528 : Nat := 4983230072969 + 3 ^ 40 * 183528 * 2
def baseEnd_183528 : Nat := 83767180051967270716423

theorem tailTrace_183528 : CollatzResearch.WordTrace tailWord_183528 prefixEnd_183528 83767180051967270716423 := by
  unfold tailWord_183528
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346908039558437466039619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4462544052744583288052825 3346908039558437466039619)
  ·
    refine ⟨5020362059337656199059429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3346908039558437466039619 5020362059337656199059429)
    ·
      refine ⟨941317886125810537323643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5020362059337656199059429 941317886125810537323643)
      ·
        refine ⟨1411976829188715805985465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941317886125810537323643 1411976829188715805985465)
        ·
          refine ⟨1058982621891536854489099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1411976829188715805985465 1058982621891536854489099)
          ·
            refine ⟨1588473932837305281733649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058982621891536854489099 1588473932837305281733649)
            ·
              refine ⟨1191355449627978961300237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1588473932837305281733649 1191355449627978961300237)
              ·
                refine ⟨446758293610492110487589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1191355449627978961300237 446758293610492110487589)
                ·
                  refine ⟨83767180051967270716423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 446758293610492110487589 83767180051967270716423)
                  ·
                    rfl

theorem cell20_183528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_183528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183528 prefixEnd_183528 := by exact prefixLift 183528
  have htrace : WordTrace (prefixWord ++ tailWord_183528) baseStart_183528 baseEnd_183528 := by
    simpa [prefixWord, tailWord_183528, baseEnd_183528] using wordTrace_append hprefix tailTrace_183528
  have hstable : (prefixWord ++ tailWord_183528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183528).length < 2 ^ (prefixWord ++ tailWord_183528).sum := by decide
  have hdescent : baseEnd_183528 < baseStart_183528 := by decide
  rcases family_descends (prefixWord ++ tailWord_183528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183576 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 3]
def baseStart_183576 : Nat := 118140960795 + 183576 * 2 ^ 59
def prefixEnd_183576 : Nat := 4983230072969 + 3 ^ 40 * 183576 * 2
def baseEnd_183576 : Nat := 83789088559892437116227

theorem tailTrace_183576 : CollatzResearch.WordTrace tailWord_183576 prefixEnd_183576 83789088559892437116227 := by
  unfold tailWord_183576
  simp only [CollatzResearch.WordTrace]
  refine ⟨3347783391471489564913291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4463711188628652753217721 3347783391471489564913291)
  ·
    refine ⟨5021675087207234347369937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3347783391471489564913291 5021675087207234347369937)
    ·
      refine ⟨3766256315405425760527453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5021675087207234347369937 3766256315405425760527453)
      ·
        refine ⟨1412346118277034660197795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3766256315405425760527453 1412346118277034660197795)
        ·
          refine ⟨2118519177415551990296693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412346118277034660197795 2118519177415551990296693)
          ·
            refine ⟨198611172882707999090315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2118519177415551990296693 198611172882707999090315)
            ·
              refine ⟨297916759324061998635473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198611172882707999090315 297916759324061998635473)
              ·
                refine ⟨223437569493046498976605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297916759324061998635473 223437569493046498976605)
                ·
                  refine ⟨83789088559892437116227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223437569493046498976605 83789088559892437116227)
                  ·
                    rfl

theorem cell20_183576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_183576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183576 prefixEnd_183576 := by exact prefixLift 183576
  have htrace : WordTrace (prefixWord ++ tailWord_183576) baseStart_183576 baseEnd_183576 := by
    simpa [prefixWord, tailWord_183576, baseEnd_183576] using wordTrace_append hprefix tailTrace_183576
  have hstable : (prefixWord ++ tailWord_183576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183576).length < 2 ^ (prefixWord ++ tailWord_183576).sum := by decide
  have hdescent : baseEnd_183576 < baseStart_183576 := by decide
  rcases family_descends (prefixWord ++ tailWord_183576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183583 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 4]
def baseStart_183583 : Nat := 118140960795 + 183583 * 2 ^ 59
def prefixEnd_183583 : Nat := 4983230072969 + 3 ^ 40 * 183583 * 2
def baseEnd_183583 : Nat := 83792283550631523882865

theorem tailTrace_183583 : CollatzResearch.WordTrace tailWord_183583 prefixEnd_183583 83792283550631523882865 := by
  unfold tailWord_183583
  simp only [CollatzResearch.WordTrace]
  refine ⟨6695822093917619325331403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4463881395945079550220935 6695822093917619325331403)
  ·
    refine ⟨10043733140876428987997105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6695822093917619325331403 10043733140876428987997105)
    ·
      refine ⟨7532799855657321740997829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10043733140876428987997105 7532799855657321740997829)
      ·
        refine ⟨1412399972935747826437093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7532799855657321740997829 1412399972935747826437093)
        ·
          refine ⟨264824994925452717456955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1412399972935747826437093 264824994925452717456955)
          ·
            refine ⟨397237492388179076185433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264824994925452717456955 397237492388179076185433)
            ·
              refine ⟨297928119291134307139075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397237492388179076185433 297928119291134307139075)
              ·
                refine ⟨446892178936701460708613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297928119291134307139075 446892178936701460708613)
                ·
                  refine ⟨83792283550631523882865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 446892178936701460708613 83792283550631523882865)
                  ·
                    rfl

theorem cell20_183583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 4].length) (baseStart_183583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183583 prefixEnd_183583 := by exact prefixLift 183583
  have htrace : WordTrace (prefixWord ++ tailWord_183583) baseStart_183583 baseEnd_183583 := by
    simpa [prefixWord, tailWord_183583, baseEnd_183583] using wordTrace_append hprefix tailTrace_183583
  have hstable : (prefixWord ++ tailWord_183583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183583).length < 2 ^ (prefixWord ++ tailWord_183583).sum := by decide
  have hdescent : baseEnd_183583 < baseStart_183583 := by decide
  rcases family_descends (prefixWord ++ tailWord_183583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183617 : List Nat := [1, 2, 5, 2, 1, 3, 1, 3, 2]
def baseStart_183617 : Nat := 118140960795 + 183617 * 2 ^ 59
def prefixEnd_183617 : Nat := 4983230072969 + 3 ^ 40 * 183617 * 2
def baseEnd_183617 : Nat := 83807802077078516749393

theorem tailTrace_183617 : CollatzResearch.WordTrace tailWord_183617 prefixEnd_183617 83807802077078516749393 := by
  unfold tailWord_183617
  simp only [CollatzResearch.WordTrace]
  refine ⟨6697062175794443132069105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4464708117196295421379403 6697062175794443132069105)
  ·
    refine ⟨5022796631845832349051829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6697062175794443132069105 5022796631845832349051829)
    ·
      refine ⟨470887184235546782723609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5022796631845832349051829 470887184235546782723609)
      ·
        refine ⟨353165388176660087042707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470887184235546782723609 353165388176660087042707)
        ·
          refine ⟨529748082264990130564061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353165388176660087042707 529748082264990130564061)
          ·
            refine ⟨198655530849371298961523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 529748082264990130564061 198655530849371298961523)
            ·
              refine ⟨297983296274056948442285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198655530849371298961523 297983296274056948442285)
              ·
                refine ⟨111743736102771355665857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297983296274056948442285 111743736102771355665857)
                ·
                  refine ⟨83807802077078516749393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111743736102771355665857 83807802077078516749393)
                  ·
                    rfl

theorem cell20_183617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 2].length) (baseStart_183617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183617 prefixEnd_183617 := by exact prefixLift 183617
  have htrace : WordTrace (prefixWord ++ tailWord_183617) baseStart_183617 baseEnd_183617 := by
    simpa [prefixWord, tailWord_183617, baseEnd_183617] using wordTrace_append hprefix tailTrace_183617
  have hstable : (prefixWord ++ tailWord_183617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183617).length < 2 ^ (prefixWord ++ tailWord_183617).sum := by decide
  have hdescent : baseEnd_183617 < baseStart_183617 := by decide
  rcases family_descends (prefixWord ++ tailWord_183617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183625 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_183625 : Nat := 118140960795 + 183625 * 2 ^ 59
def prefixEnd_183625 : Nat := 4983230072969 + 3 ^ 40 * 183625 * 2
def baseEnd_183625 : Nat := 83811453495066044482693

theorem tailTrace_183625 : CollatzResearch.WordTrace tailWord_183625 prefixEnd_183625 83811453495066044482693 := by
  unfold tailWord_183625
  simp only [CollatzResearch.WordTrace]
  refine ⟨6697353959765460498360329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4464902639843640332240219 6697353959765460498360329)
  ·
    refine ⟨5023015469824095373770247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6697353959765460498360329 5023015469824095373770247)
    ·
      refine ⟨7534523204736143060655371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5023015469824095373770247 7534523204736143060655371)
      ·
        refine ⟨11301784807104214590983057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7534523204736143060655371 11301784807104214590983057)
        ·
          refine ⟨8476338605328160943237293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11301784807104214590983057 8476338605328160943237293)
          ·
            refine ⟨3178626976998060353713985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8476338605328160943237293 3178626976998060353713985)
            ·
              refine ⟨2383970232748545265285489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3178626976998060353713985 2383970232748545265285489)
              ·
                refine ⟨1787977674561408948964117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2383970232748545265285489 1787977674561408948964117)
                ·
                  refine ⟨83811453495066044482693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1787977674561408948964117 83811453495066044482693)
                  ·
                    rfl

theorem cell20_183625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_183625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183625 prefixEnd_183625 := by exact prefixLift 183625
  have htrace : WordTrace (prefixWord ++ tailWord_183625) baseStart_183625 baseEnd_183625 := by
    simpa [prefixWord, tailWord_183625, baseEnd_183625] using wordTrace_append hprefix tailTrace_183625
  have hstable : (prefixWord ++ tailWord_183625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183625).length < 2 ^ (prefixWord ++ tailWord_183625).sum := by decide
  have hdescent : baseEnd_183625 < baseStart_183625 := by decide
  rcases family_descends (prefixWord ++ tailWord_183625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183642 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_183642 : Nat := 118140960795 + 183642 * 2 ^ 59
def prefixEnd_183642 : Nat := 4983230072969 + 3 ^ 40 * 183642 * 2
def baseEnd_183642 : Nat := 83819212758289540915957

theorem tailTrace_183642 : CollatzResearch.WordTrace tailWord_183642 prefixEnd_183642 83819212758289540915957 := by
  unfold tailWord_183642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1674493500175968100432295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4465316000469248267819453 1674493500175968100432295)
  ·
    refine ⟨2511740250263952150648443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1674493500175968100432295 2511740250263952150648443)
    ·
      refine ⟨3767610375395928225972665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2511740250263952150648443 3767610375395928225972665)
      ·
        refine ⟨2825707781546946169479499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3767610375395928225972665 2825707781546946169479499)
        ·
          refine ⟨4238561672320419254219249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2825707781546946169479499 4238561672320419254219249)
          ·
            refine ⟨3178921254240314440664437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4238561672320419254219249 3178921254240314440664437)
            ·
              refine ⟨298023867585029478812291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3178921254240314440664437 298023867585029478812291)
              ·
                refine ⟨447035801377544218218437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298023867585029478812291 447035801377544218218437)
                ·
                  refine ⟨83819212758289540915957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447035801377544218218437 83819212758289540915957)
                  ·
                    rfl

theorem cell20_183642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_183642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183642 prefixEnd_183642 := by exact prefixLift 183642
  have htrace : WordTrace (prefixWord ++ tailWord_183642) baseStart_183642 baseEnd_183642 := by
    simpa [prefixWord, tailWord_183642, baseEnd_183642] using wordTrace_append hprefix tailTrace_183642
  have hstable : (prefixWord ++ tailWord_183642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183642).length < 2 ^ (prefixWord ++ tailWord_183642).sum := by decide
  have hdescent : baseEnd_183642 < baseStart_183642 := by decide
  rcases family_descends (prefixWord ++ tailWord_183642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183652 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 3]
def baseStart_183652 : Nat := 118140960795 + 183652 * 2 ^ 59
def prefixEnd_183652 : Nat := 4983230072969 + 3 ^ 40 * 183652 * 2
def baseEnd_183652 : Nat := 83823777030773950582583

theorem tailTrace_183652 : CollatzResearch.WordTrace tailWord_183652 prefixEnd_183652 83823777030773950582583 := by
  unfold tailWord_183652
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349169365333822054796605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4465559153778429406395473 3349169365333822054796605)
  ·
    refine ⟨1255938512000183270548727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3349169365333822054796605 1255938512000183270548727)
    ·
      refine ⟨1883907768000274905823091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1255938512000183270548727 1883907768000274905823091)
      ·
        refine ⟨2825861652000412358734637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1883907768000274905823091 2825861652000412358734637)
        ·
          refine ⟨1059698119500154634525489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2825861652000412358734637 1059698119500154634525489)
          ·
            refine ⟨794773589625115975894117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1059698119500154634525489 794773589625115975894117)
            ·
              refine ⟨149020048054709245480147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 794773589625115975894117 149020048054709245480147)
              ·
                refine ⟨223530072082063868220221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149020048054709245480147 223530072082063868220221)
                ·
                  refine ⟨83823777030773950582583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223530072082063868220221 83823777030773950582583)
                  ·
                    rfl

theorem cell20_183652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_183652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183652 prefixEnd_183652 := by exact prefixLift 183652
  have htrace : WordTrace (prefixWord ++ tailWord_183652) baseStart_183652 baseEnd_183652 := by
    simpa [prefixWord, tailWord_183652, baseEnd_183652] using wordTrace_append hprefix tailTrace_183652
  have hstable : (prefixWord ++ tailWord_183652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183652).length < 2 ^ (prefixWord ++ tailWord_183652).sum := by decide
  have hdescent : baseEnd_183652 < baseStart_183652 := by decide
  rcases family_descends (prefixWord ++ tailWord_183652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183663 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_183663 : Nat := 118140960795 + 183663 * 2 ^ 59
def prefixEnd_183663 : Nat := 4983230072969 + 3 ^ 40 * 183663 * 2
def baseEnd_183663 : Nat := 83828797730506801215871

theorem tailTrace_183663 : CollatzResearch.WordTrace tailWord_183663 prefixEnd_183663 83828797730506801215871 := by
  unfold tailWord_183663
  simp only [CollatzResearch.WordTrace]
  refine ⟨6698739933627792988243643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4465826622418528658829095 6698739933627792988243643)
  ·
    refine ⟨10048109900441689482365465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6698739933627792988243643 10048109900441689482365465)
    ·
      refine ⟨7536082425331267111774099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10048109900441689482365465 7536082425331267111774099)
      ·
        refine ⟨11304123637996900667661149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7536082425331267111774099 11304123637996900667661149)
        ·
          refine ⟨4239046364248837750372931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11304123637996900667661149 4239046364248837750372931)
          ·
            refine ⟨6358569546373256625559397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239046364248837750372931 6358569546373256625559397)
            ·
              refine ⟨1192231789944985617292387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6358569546373256625559397 1192231789944985617292387)
              ·
                refine ⟨1788347684917478425938581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192231789944985617292387 1788347684917478425938581)
                ·
                  refine ⟨83828797730506801215871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1788347684917478425938581 83828797730506801215871)
                  ·
                    rfl

theorem cell20_183663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_183663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183663 prefixEnd_183663 := by exact prefixLift 183663
  have htrace : WordTrace (prefixWord ++ tailWord_183663) baseStart_183663 baseEnd_183663 := by
    simpa [prefixWord, tailWord_183663, baseEnd_183663] using wordTrace_append hprefix tailTrace_183663
  have hstable : (prefixWord ++ tailWord_183663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183663).length < 2 ^ (prefixWord ++ tailWord_183663).sum := by decide
  have hdescent : baseEnd_183663 < baseStart_183663 := by decide
  rcases family_descends (prefixWord ++ tailWord_183663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183711 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 3]
def baseStart_183711 : Nat := 118140960795 + 183711 * 2 ^ 59
def prefixEnd_183711 : Nat := 4983230072969 + 3 ^ 40 * 183711 * 2
def baseEnd_183711 : Nat := 83850706238431967615675

theorem tailTrace_183711 : CollatzResearch.WordTrace tailWord_183711 prefixEnd_183711 83850706238431967615675 := by
  unfold tailWord_183711
  simp only [CollatzResearch.WordTrace]
  refine ⟨6700490637453897185990987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4466993758302598123993991 6700490637453897185990987)
  ·
    refine ⟨10050735956180845778986481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6700490637453897185990987 10050735956180845778986481)
    ·
      refine ⟨7538051967135634334239861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10050735956180845778986481 7538051967135634334239861)
      ·
        refine ⟨706692371918965718834987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7538051967135634334239861 706692371918965718834987)
        ·
          refine ⟨1060038557878448578252481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706692371918965718834987 1060038557878448578252481)
          ·
            refine ⟨795028918408836433689361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060038557878448578252481 795028918408836433689361)
            ·
              refine ⟨596271688806627325267021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795028918408836433689361 596271688806627325267021)
              ·
                refine ⟨223601883302485246975133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 596271688806627325267021 223601883302485246975133)
                ·
                  refine ⟨83850706238431967615675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223601883302485246975133 83850706238431967615675)
                  ·
                    rfl

theorem cell20_183711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 3].length) (baseStart_183711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183711 prefixEnd_183711 := by exact prefixLift 183711
  have htrace : WordTrace (prefixWord ++ tailWord_183711) baseStart_183711 baseEnd_183711 := by
    simpa [prefixWord, tailWord_183711, baseEnd_183711] using wordTrace_append hprefix tailTrace_183711
  have hstable : (prefixWord ++ tailWord_183711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183711).length < 2 ^ (prefixWord ++ tailWord_183711).sum := by decide
  have hdescent : baseEnd_183711 < baseStart_183711 := by decide
  rcases family_descends (prefixWord ++ tailWord_183711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183735 : List Nat := [1, 1, 3, 1, 3, 2, 4, 3, 2]
def baseStart_183735 : Nat := 118140960795 + 183735 * 2 ^ 59
def prefixEnd_183735 : Nat := 4983230072969 + 3 ^ 40 * 183735 * 2
def baseEnd_183735 : Nat := 83861660492394550815577

theorem tailTrace_183735 : CollatzResearch.WordTrace tailWord_183735 prefixEnd_183735 83861660492394550815577 := by
  unfold tailWord_183735
  simp only [CollatzResearch.WordTrace]
  refine ⟨6701365989366949284864659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4467577326244632856576439 6701365989366949284864659)
  ·
    refine ⟨10052048984050423927296989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6701365989366949284864659 10052048984050423927296989)
    ·
      refine ⟨3769518369018908972736371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10052048984050423927296989 3769518369018908972736371)
      ·
        refine ⟨5654277553528363459104557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3769518369018908972736371 5654277553528363459104557)
        ·
          refine ⟨2120354082573136297164209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5654277553528363459104557 2120354082573136297164209)
          ·
            refine ⟨1590265561929852222873157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2120354082573136297164209 1590265561929852222873157)
            ·
              refine ⟨298174792861847291788717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1590265561929852222873157 298174792861847291788717)
              ·
                refine ⟨111815547323192734420769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298174792861847291788717 111815547323192734420769)
                ·
                  refine ⟨83861660492394550815577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111815547323192734420769 83861660492394550815577)
                  ·
                    rfl

theorem cell20_183735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 2].length) (baseStart_183735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183735 prefixEnd_183735 := by exact prefixLift 183735
  have htrace : WordTrace (prefixWord ++ tailWord_183735) baseStart_183735 baseEnd_183735 := by
    simpa [prefixWord, tailWord_183735, baseEnd_183735] using wordTrace_append hprefix tailTrace_183735
  have hstable : (prefixWord ++ tailWord_183735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183735).length < 2 ^ (prefixWord ++ tailWord_183735).sum := by decide
  have hdescent : baseEnd_183735 < baseStart_183735 := by decide
  rcases family_descends (prefixWord ++ tailWord_183735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183756 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_183756 : Nat := 118140960795 + 183756 * 2 ^ 59
def prefixEnd_183756 : Nat := 4983230072969 + 3 ^ 40 * 183756 * 2
def baseEnd_183756 : Nat := 83871245464611811115491

theorem tailTrace_183756 : CollatzResearch.WordTrace tailWord_183756 prefixEnd_183756 83871245464611811115491 := by
  unfold tailWord_183756
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351065961145434935689561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4468087948193913247586081 3351065961145434935689561)
  ·
    refine ⟨2513299470859076201767171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3351065961145434935689561 2513299470859076201767171)
    ·
      refine ⟨3769949206288614302650757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2513299470859076201767171 3769949206288614302650757)
      ·
        refine ⟨706865476179115181747017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3769949206288614302650757 706865476179115181747017)
        ·
          refine ⟨530149107134336386310263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706865476179115181747017 530149107134336386310263)
          ·
            refine ⟨795223660701504579465395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530149107134336386310263 795223660701504579465395)
            ·
              refine ⟨1192835491052256869198093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795223660701504579465395 1192835491052256869198093)
              ·
                refine ⟨447313309144596325949285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1192835491052256869198093 447313309144596325949285)
                ·
                  refine ⟨83871245464611811115491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447313309144596325949285 83871245464611811115491)
                  ·
                    rfl

theorem cell20_183756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_183756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183756 prefixEnd_183756 := by exact prefixLift 183756
  have htrace : WordTrace (prefixWord ++ tailWord_183756) baseStart_183756 baseEnd_183756 := by
    simpa [prefixWord, tailWord_183756, baseEnd_183756] using wordTrace_append hprefix tailTrace_183756
  have hstable : (prefixWord ++ tailWord_183756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183756).length < 2 ^ (prefixWord ++ tailWord_183756).sum := by decide
  have hdescent : baseEnd_183756 < baseStart_183756 := by decide
  rcases family_descends (prefixWord ++ tailWord_183756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183862 : List Nat := [5, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_183862 : Nat := 118140960795 + 183862 * 2 ^ 59
def prefixEnd_183862 : Nat := 4983230072969 + 3 ^ 40 * 183862 * 2
def baseEnd_183862 : Nat := 83919626752946553581725

theorem tailTrace_183862 : CollatzResearch.WordTrace tailWord_183862 prefixEnd_183862 83919626752946553581725 := by
  unfold tailWord_183862
  simp only [CollatzResearch.WordTrace]
  refine ⟨419124878744178123421115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4470665373271233316491893 419124878744178123421115)
  ·
    refine ⟨628687318116267185131673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 419124878744178123421115 628687318116267185131673)
    ·
      refine ⟨471515488587200388848755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 628687318116267185131673 471515488587200388848755)
      ·
        refine ⟨707273232880800583273133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471515488587200388848755 707273232880800583273133)
        ·
          refine ⟨265227462330300218727425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 707273232880800583273133 265227462330300218727425)
          ·
            refine ⟨198920596747725164045569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265227462330300218727425 198920596747725164045569)
            ·
              refine ⟨149190447560793873034177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198920596747725164045569 149190447560793873034177)
              ·
                refine ⟨111892835670595404775633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149190447560793873034177 111892835670595404775633)
                ·
                  refine ⟨83919626752946553581725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111892835670595404775633 83919626752946553581725)
                  ·
                    rfl

theorem cell20_183862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_183862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183862 prefixEnd_183862 := by exact prefixLift 183862
  have htrace : WordTrace (prefixWord ++ tailWord_183862) baseStart_183862 baseEnd_183862 := by
    simpa [prefixWord, tailWord_183862, baseEnd_183862] using wordTrace_append hprefix tailTrace_183862
  have hstable : (prefixWord ++ tailWord_183862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183862).length < 2 ^ (prefixWord ++ tailWord_183862).sum := by decide
  have hdescent : baseEnd_183862 < baseStart_183862 := by decide
  rcases family_descends (prefixWord ++ tailWord_183862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183863 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 3]
def baseStart_183863 : Nat := 118140960795 + 183863 * 2 ^ 59
def prefixEnd_183863 : Nat := 4983230072969 + 3 ^ 40 * 183863 * 2
def baseEnd_183863 : Nat := 83920083180194994548387

theorem tailTrace_183863 : CollatzResearch.WordTrace tailWord_183863 prefixEnd_183863 83920083180194994548387 := by
  unfold tailWord_183863
  simp only [CollatzResearch.WordTrace]
  refine ⟨6706034532903227145524243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4470689688602151430349495 6706034532903227145524243)
  ·
    refine ⟨10059051799354840718286365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6706034532903227145524243 10059051799354840718286365)
    ·
      refine ⟨3772144424758065269357387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10059051799354840718286365 3772144424758065269357387)
      ·
        refine ⟨5658216637137097904036081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3772144424758065269357387 5658216637137097904036081)
        ·
          refine ⟨4243662477852823428027061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5658216637137097904036081 4243662477852823428027061)
          ·
            refine ⟨397843357298702196377537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4243662477852823428027061 397843357298702196377537)
            ·
              refine ⟨298382517974026647283153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397843357298702196377537 298382517974026647283153)
              ·
                refine ⟨223786888480519985462365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298382517974026647283153 223786888480519985462365)
                ·
                  refine ⟨83920083180194994548387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223786888480519985462365 83920083180194994548387)
                  ·
                    rfl

theorem cell20_183863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 3].length) (baseStart_183863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183863 prefixEnd_183863 := by exact prefixLift 183863
  have htrace : WordTrace (prefixWord ++ tailWord_183863) baseStart_183863 baseEnd_183863 := by
    simpa [prefixWord, tailWord_183863, baseEnd_183863] using wordTrace_append hprefix tailTrace_183863
  have hstable : (prefixWord ++ tailWord_183863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183863).length < 2 ^ (prefixWord ++ tailWord_183863).sum := by decide
  have hdescent : baseEnd_183863 < baseStart_183863 := by decide
  rcases family_descends (prefixWord ++ tailWord_183863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183898 : List Nat := [3, 1, 1, 2, 1, 1, 1, 10]
def baseStart_183898 : Nat := 118140960795 + 183898 * 2 ^ 59
def prefixEnd_183898 : Nat := 4983230072969 + 3 ^ 40 * 183898 * 2
def baseEnd_183898 : Nat := 27978686044630142793859

theorem tailTrace_183898 : CollatzResearch.WordTrace tailWord_183898 prefixEnd_183898 27978686044630142793859 := by
  unfold tailWord_183898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676827771944107030762087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4471540725184285415365565 1676827771944107030762087)
  ·
    refine ⟨2515241657916160546143131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1676827771944107030762087 2515241657916160546143131)
    ·
      refine ⟨3772862486874240819214697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2515241657916160546143131 3772862486874240819214697)
      ·
        refine ⟨2829646865155680614411023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3772862486874240819214697 2829646865155680614411023)
        ·
          refine ⟨4244470297733520921616535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829646865155680614411023 4244470297733520921616535)
          ·
            refine ⟨6366705446600281382424803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4244470297733520921616535 6366705446600281382424803)
            ·
              refine ⟨9550058169900422073637205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6366705446600281382424803 9550058169900422073637205)
              ·
                refine ⟨27978686044630142793859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9550058169900422073637205 27978686044630142793859)
                ·
                  rfl

theorem cell20_183898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_183898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183898 prefixEnd_183898 := by exact prefixLift 183898
  have htrace : WordTrace (prefixWord ++ tailWord_183898) baseStart_183898 baseEnd_183898 := by
    simpa [prefixWord, tailWord_183898, baseEnd_183898] using wordTrace_append hprefix tailTrace_183898
  have hstable : (prefixWord ++ tailWord_183898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183898).length < 2 ^ (prefixWord ++ tailWord_183898).sum := by decide
  have hdescent : baseEnd_183898 < baseStart_183898 := by decide
  rcases family_descends (prefixWord ++ tailWord_183898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183925 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 4]
def baseStart_183925 : Nat := 118140960795 + 183925 * 2 ^ 59
def prefixEnd_183925 : Nat := 4983230072969 + 3 ^ 40 * 183925 * 2
def baseEnd_183925 : Nat := 83948381669598334481467

theorem tailTrace_183925 : CollatzResearch.WordTrace tailWord_183925 prefixEnd_183925 83948381669598334481467 := by
  unfold tailWord_183925
  simp only [CollatzResearch.WordTrace]
  refine ⟨6708295858678611734281229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4472197239119074489520819 6708295858678611734281229)
  ·
    refine ⟨2515610947004479400355461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6708295858678611734281229 2515610947004479400355461)
    ·
      refine ⟨471677052563339887566649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2515610947004479400355461 471677052563339887566649)
      ·
        refine ⟨353757789422504915674987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471677052563339887566649 353757789422504915674987)
        ·
          refine ⟨530636684133757373512481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353757789422504915674987 530636684133757373512481)
          ·
            refine ⟨397977513100318030134361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530636684133757373512481 397977513100318030134361)
            ·
              refine ⟨298483134825238522600771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397977513100318030134361 298483134825238522600771)
              ·
                refine ⟨447724702237857783901157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298483134825238522600771 447724702237857783901157)
                ·
                  refine ⟨83948381669598334481467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447724702237857783901157 83948381669598334481467)
                  ·
                    rfl

theorem cell20_183925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_183925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183925 prefixEnd_183925 := by exact prefixLift 183925
  have htrace : WordTrace (prefixWord ++ tailWord_183925) baseStart_183925 baseEnd_183925 := by
    simpa [prefixWord, tailWord_183925, baseEnd_183925] using wordTrace_append hprefix tailTrace_183925
  have hstable : (prefixWord ++ tailWord_183925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183925).length < 2 ^ (prefixWord ++ tailWord_183925).sum := by decide
  have hdescent : baseEnd_183925 < baseStart_183925 := by decide
  rcases family_descends (prefixWord ++ tailWord_183925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183936 : List Nat := [2, 1, 1, 2, 1, 4, 2, 7]
def baseStart_183936 : Nat := 118140960795 + 183936 * 2 ^ 59
def prefixEnd_183936 : Nat := 4983230072969 + 3 ^ 40 * 183936 * 2
def baseEnd_183936 : Nat := 27984467456443728371585

theorem tailTrace_183936 : CollatzResearch.WordTrace tailWord_183936 prefixEnd_183936 27984467456443728371585 := by
  unfold tailWord_183936
  simp only [CollatzResearch.WordTrace]
  refine ⟨3354348530819380306465831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4472464707759173741954441 3354348530819380306465831)
  ·
    refine ⟨5031522796229070459698747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3354348530819380306465831 5031522796229070459698747)
    ·
      refine ⟨7547284194343605689548121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5031522796229070459698747 7547284194343605689548121)
      ·
        refine ⟨5660463145757704267161091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7547284194343605689548121 5660463145757704267161091)
        ·
          refine ⟨8490694718636556400741637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5660463145757704267161091 8490694718636556400741637)
          ·
            refine ⟨1592005259744354325139057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8490694718636556400741637 1592005259744354325139057)
            ·
              refine ⟨1194003944808265743854293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592005259744354325139057 1194003944808265743854293)
              ·
                refine ⟨27984467456443728371585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1194003944808265743854293 27984467456443728371585)
                ·
                  rfl

theorem cell20_183936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_183936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183936 prefixEnd_183936 := by exact prefixLift 183936
  have htrace : WordTrace (prefixWord ++ tailWord_183936) baseStart_183936 baseEnd_183936 := by
    simpa [prefixWord, tailWord_183936, baseEnd_183936] using wordTrace_append hprefix tailTrace_183936
  have hstable : (prefixWord ++ tailWord_183936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183936).length < 2 ^ (prefixWord ++ tailWord_183936).sum := by decide
  have hdescent : baseEnd_183936 < baseStart_183936 := by decide
  rcases family_descends (prefixWord ++ tailWord_183936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183946 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_183946 : Nat := 118140960795 + 183946 * 2 ^ 59
def prefixEnd_183946 : Nat := 4983230072969 + 3 ^ 40 * 183946 * 2
def baseEnd_183946 : Nat := 83957966641815594781381

theorem tailTrace_183946 : CollatzResearch.WordTrace tailWord_183946 prefixEnd_183946 83957966641815594781381 := by
  unfold tailWord_183946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677265447900633080198923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4472707861068354880530461 1677265447900633080198923)
  ·
    refine ⟨2515898171850949620298385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1677265447900633080198923 2515898171850949620298385)
    ·
      refine ⟨1886923628888212215223789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2515898171850949620298385 1886923628888212215223789)
      ·
        refine ⟨707596360833079580708921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1886923628888212215223789 707596360833079580708921)
        ·
          refine ⟨530697270624809685531691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 707596360833079580708921 530697270624809685531691)
          ·
            refine ⟨796045905937214528297537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530697270624809685531691 796045905937214528297537)
            ·
              refine ⟨597034429452910896223153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796045905937214528297537 597034429452910896223153)
              ·
                refine ⟨447775822089683172167365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597034429452910896223153 447775822089683172167365)
                ·
                  refine ⟨83957966641815594781381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447775822089683172167365 83957966641815594781381)
                  ·
                    rfl

theorem cell20_183946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_183946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183946 prefixEnd_183946 := by exact prefixLift 183946
  have htrace : WordTrace (prefixWord ++ tailWord_183946) baseStart_183946 baseEnd_183946 := by
    simpa [prefixWord, tailWord_183946, baseEnd_183946] using wordTrace_append hprefix tailTrace_183946
  have hstable : (prefixWord ++ tailWord_183946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183946).length < 2 ^ (prefixWord ++ tailWord_183946).sum := by decide
  have hdescent : baseEnd_183946 < baseStart_183946 := by decide
  rcases family_descends (prefixWord ++ tailWord_183946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183960 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_183960 : Nat := 118140960795 + 183960 * 2 ^ 59
def prefixEnd_183960 : Nat := 4983230072969 + 3 ^ 40 * 183960 * 2
def baseEnd_183960 : Nat := 83964356623293768314657

theorem tailTrace_183960 : CollatzResearch.WordTrace tailWord_183960 prefixEnd_183960 83964356623293768314657 := by
  unfold tailWord_183960
  simp only [CollatzResearch.WordTrace]
  refine ⟨3354786206775906355902667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4473048275701208474536889 3354786206775906355902667)
  ·
    refine ⟨5032179310163859533854001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3354786206775906355902667 5032179310163859533854001)
    ·
      refine ⟨3774134482622894650390501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5032179310163859533854001 3774134482622894650390501)
      ·
        refine ⟨707650215491792746948219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3774134482622894650390501 707650215491792746948219)
        ·
          refine ⟨1061475323237689120422329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707650215491792746948219 1061475323237689120422329)
          ·
            refine ⟨796106492428266840316747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1061475323237689120422329 796106492428266840316747)
            ·
              refine ⟨1194159738642400260475121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796106492428266840316747 1194159738642400260475121)
              ·
                refine ⟨895619803981800195356341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194159738642400260475121 895619803981800195356341)
                ·
                  refine ⟨83964356623293768314657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 895619803981800195356341 83964356623293768314657)
                  ·
                    rfl

theorem cell20_183960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_183960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183960 prefixEnd_183960 := by exact prefixLift 183960
  have htrace : WordTrace (prefixWord ++ tailWord_183960) baseStart_183960 baseEnd_183960 := by
    simpa [prefixWord, tailWord_183960, baseEnd_183960] using wordTrace_append hprefix tailTrace_183960
  have hstable : (prefixWord ++ tailWord_183960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183960).length < 2 ^ (prefixWord ++ tailWord_183960).sum := by decide
  have hdescent : baseEnd_183960 < baseStart_183960 := by decide
  rcases family_descends (prefixWord ++ tailWord_183960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183976 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 4]
def baseStart_183976 : Nat := 118140960795 + 183976 * 2 ^ 59
def prefixEnd_183976 : Nat := 4983230072969 + 3 ^ 40 * 183976 * 2
def baseEnd_183976 : Nat := 83971659459268823781259

theorem tailTrace_183976 : CollatzResearch.WordTrace tailWord_183976 prefixEnd_183976 83971659459268823781259 := by
  unfold tailWord_183976
  simp only [CollatzResearch.WordTrace]
  refine ⟨3355077990746923722193891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4473437320995898296258521 3355077990746923722193891)
  ·
    refine ⟨5032616986120385583290837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3355077990746923722193891 5032616986120385583290837)
    ·
      refine ⟨117951960612196537108379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5032616986120385583290837 117951960612196537108379)
      ·
        refine ⟨176927940918294805662569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117951960612196537108379 176927940918294805662569)
        ·
          refine ⟨132695955688721104246927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176927940918294805662569 132695955688721104246927)
          ·
            refine ⟨199043933533081656370391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132695955688721104246927 199043933533081656370391)
            ·
              refine ⟨298565900299622484555587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199043933533081656370391 298565900299622484555587)
              ·
                refine ⟨447848850449433726833381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298565900299622484555587 447848850449433726833381)
                ·
                  refine ⟨83971659459268823781259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447848850449433726833381 83971659459268823781259)
                  ·
                    rfl

theorem cell20_183976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 4].length) (baseStart_183976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183976 prefixEnd_183976 := by exact prefixLift 183976
  have htrace : WordTrace (prefixWord ++ tailWord_183976) baseStart_183976 baseEnd_183976 := by
    simpa [prefixWord, tailWord_183976, baseEnd_183976] using wordTrace_append hprefix tailTrace_183976
  have hstable : (prefixWord ++ tailWord_183976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183976).length < 2 ^ (prefixWord ++ tailWord_183976).sum := by decide
  have hdescent : baseEnd_183976 < baseStart_183976 := by decide
  rcases family_descends (prefixWord ++ tailWord_183976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183984 : List Nat := [2, 1, 1, 1, 2, 1, 4, 6, 2]
def baseStart_183984 : Nat := 118140960795 + 183984 * 2 ^ 59
def prefixEnd_183984 : Nat := 4983230072969 + 3 ^ 40 * 183984 * 2
def baseEnd_183984 : Nat := 83975310877256351514559

theorem tailTrace_183984 : CollatzResearch.WordTrace tailWord_183984 prefixEnd_183984 83975310877256351514559 := by
  unfold tailWord_183984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3355223882732432405339503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4473631843643243207119337 3355223882732432405339503)
  ·
    refine ⟨5032835824098648608009255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3355223882732432405339503 5032835824098648608009255)
    ·
      refine ⟨7549253736147972912013883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5032835824098648608009255 7549253736147972912013883)
      ·
        refine ⟨11323880604221959368020825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7549253736147972912013883 11323880604221959368020825)
        ·
          refine ⟨8492910453166469526015619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11323880604221959368020825 8492910453166469526015619)
          ·
            refine ⟨12739365679749704289023429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8492910453166469526015619 12739365679749704289023429)
            ·
              refine ⟨2388631064953069554191893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12739365679749704289023429 2388631064953069554191893)
              ·
                refine ⟨111967081169675135352745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2388631064953069554191893 111967081169675135352745)
                ·
                  refine ⟨83975310877256351514559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111967081169675135352745 83975310877256351514559)
                  ·
                    rfl

theorem cell20_183984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 2].length) (baseStart_183984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183984 prefixEnd_183984 := by exact prefixLift 183984
  have htrace : WordTrace (prefixWord ++ tailWord_183984) baseStart_183984 baseEnd_183984 := by
    simpa [prefixWord, tailWord_183984, baseEnd_183984] using wordTrace_append hprefix tailTrace_183984
  have hstable : (prefixWord ++ tailWord_183984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183984).length < 2 ^ (prefixWord ++ tailWord_183984).sum := by decide
  have hdescent : baseEnd_183984 < baseStart_183984 := by decide
  rcases family_descends (prefixWord ++ tailWord_183984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183990 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_183990 : Nat := 118140960795 + 183990 * 2 ^ 59
def prefixEnd_183990 : Nat := 4983230072969 + 3 ^ 40 * 183990 * 2
def baseEnd_183990 : Nat := 83978049440746997314535

theorem tailTrace_183990 : CollatzResearch.WordTrace tailWord_183990 prefixEnd_183990 83978049440746997314535 := by
  unfold tailWord_183990
  simp only [CollatzResearch.WordTrace]
  refine ⟨419416662715195489712339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4473777735628751890264949 419416662715195489712339)
  ·
    refine ⟨629124994072793234568509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 419416662715195489712339 629124994072793234568509)
    ·
      refine ⟨235921872777297462963191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 629124994072793234568509 235921872777297462963191)
      ·
        refine ⟨353882809165946194444787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235921872777297462963191 353882809165946194444787)
        ·
          refine ⟨530824213748919291667181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353882809165946194444787 530824213748919291667181)
          ·
            refine ⟨199059080155844734375193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 530824213748919291667181 199059080155844734375193)
            ·
              refine ⟨149294310116883550781395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199059080155844734375193 149294310116883550781395)
              ·
                refine ⟨223941465175325326172093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149294310116883550781395 223941465175325326172093)
                ·
                  refine ⟨83978049440746997314535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223941465175325326172093 83978049440746997314535)
                  ·
                    rfl

theorem cell20_183990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_183990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183990 prefixEnd_183990 := by exact prefixLift 183990
  have htrace : WordTrace (prefixWord ++ tailWord_183990) baseStart_183990 baseEnd_183990 := by
    simpa [prefixWord, tailWord_183990, baseEnd_183990] using wordTrace_append hprefix tailTrace_183990
  have hstable : (prefixWord ++ tailWord_183990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183990).length < 2 ^ (prefixWord ++ tailWord_183990).sum := by decide
  have hdescent : baseEnd_183990 < baseStart_183990 := by decide
  rcases family_descends (prefixWord ++ tailWord_183990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183991 : List Nat := [1, 1, 3, 1, 5, 2, 2, 5]
def baseStart_183991 : Nat := 118140960795 + 183991 * 2 ^ 59
def prefixEnd_183991 : Nat := 4983230072969 + 3 ^ 40 * 183991 * 2
def baseEnd_183991 : Nat := 27992835289331812760399

theorem tailTrace_183991 : CollatzResearch.WordTrace tailWord_183991 prefixEnd_183991 27992835289331812760399 := by
  unfold tailWord_183991
  simp only [CollatzResearch.WordTrace]
  refine ⟨6710703076439505006183827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4473802050959670004122551 6710703076439505006183827)
  ·
    refine ⟨10066054614659257509275741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6710703076439505006183827 10066054614659257509275741)
    ·
      refine ⟨3774770480497221565978403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10066054614659257509275741 3774770480497221565978403)
      ·
        refine ⟨5662155720745832348967605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3774770480497221565978403 5662155720745832348967605)
        ·
          refine ⟨530827098819921782715713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5662155720745832348967605 530827098819921782715713)
          ·
            refine ⟨398120324114941337036785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530827098819921782715713 398120324114941337036785)
            ·
              refine ⟨298590243086206002777589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398120324114941337036785 298590243086206002777589)
              ·
                refine ⟨27992835289331812760399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 298590243086206002777589 27992835289331812760399)
                ·
                  rfl

theorem cell20_183991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_183991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183991 prefixEnd_183991 := by exact prefixLift 183991
  have htrace : WordTrace (prefixWord ++ tailWord_183991) baseStart_183991 baseEnd_183991 := by
    simpa [prefixWord, tailWord_183991, baseEnd_183991] using wordTrace_append hprefix tailTrace_183991
  have hstable : (prefixWord ++ tailWord_183991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183991).length < 2 ^ (prefixWord ++ tailWord_183991).sum := by decide
  have hdescent : baseEnd_183991 < baseStart_183991 := by decide
  rcases family_descends (prefixWord ++ tailWord_183991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183994 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_183994 : Nat := 118140960795 + 183994 * 2 ^ 59
def prefixEnd_183994 : Nat := 4983230072969 + 3 ^ 40 * 183994 * 2
def baseEnd_183994 : Nat := 83979875149740761181185

theorem tailTrace_183994 : CollatzResearch.WordTrace tailWord_183994 prefixEnd_183994 83979875149740761181185 := by
  unfold tailWord_183994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677703123857159129635759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4473874996952424345695357 1677703123857159129635759)
  ·
    refine ⟨2516554685785738694453639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1677703123857159129635759 2516554685785738694453639)
    ·
      refine ⟨3774832028678608041680459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2516554685785738694453639 3774832028678608041680459)
      ·
        refine ⟨5662248043017912062520689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3774832028678608041680459 5662248043017912062520689)
        ·
          refine ⟨4246686032263434046890517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5662248043017912062520689 4246686032263434046890517)
          ·
            refine ⟨199063407762348470947993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4246686032263434046890517 199063407762348470947993)
            ·
              refine ⟨149297555821761353210995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199063407762348470947993 149297555821761353210995)
              ·
                refine ⟨223946333732642029816493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149297555821761353210995 223946333732642029816493)
                ·
                  refine ⟨83979875149740761181185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223946333732642029816493 83979875149740761181185)
                  ·
                    rfl

theorem cell20_183994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_183994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_183994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_183994 prefixEnd_183994 := by exact prefixLift 183994
  have htrace : WordTrace (prefixWord ++ tailWord_183994) baseStart_183994 baseEnd_183994 := by
    simpa [prefixWord, tailWord_183994, baseEnd_183994] using wordTrace_append hprefix tailTrace_183994
  have hstable : (prefixWord ++ tailWord_183994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183994).length < 2 ^ (prefixWord ++ tailWord_183994).sum := by decide
  have hdescent : baseEnd_183994 < baseStart_183994 := by decide
  rcases family_descends (prefixWord ++ tailWord_183994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184029 : List Nat := [1, 4, 3, 3, 9]
def baseStart_184029 : Nat := 118140960795 + 184029 * 2 ^ 59
def prefixEnd_184029 : Nat := 4983230072969 + 3 ^ 40 * 184029 * 2
def baseEnd_184029 : Nat := 1036985803746125864375

theorem tailTrace_184029 : CollatzResearch.WordTrace tailWord_184029 prefixEnd_184029 1036985803746125864375 := by
  unfold tailWord_184029
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712089050301837496067141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4474726033534558330711427 6712089050301837496067141)
  ·
    refine ⟨1258516696931594530512589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6712089050301837496067141 1258516696931594530512589)
    ·
      refine ⟨471943761349347948942221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1258516696931594530512589 471943761349347948942221)
      ·
        refine ⟨176978910506005480853333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471943761349347948942221 176978910506005480853333)
        ·
          refine ⟨1036985803746125864375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 176978910506005480853333 1036985803746125864375)
          ·
            rfl

theorem cell20_184029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 9].length) (baseStart_184029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184029 prefixEnd_184029 := by exact prefixLift 184029
  have htrace : WordTrace (prefixWord ++ tailWord_184029) baseStart_184029 baseEnd_184029 := by
    simpa [prefixWord, tailWord_184029, baseEnd_184029] using wordTrace_append hprefix tailTrace_184029
  have hstable : (prefixWord ++ tailWord_184029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184029).length < 2 ^ (prefixWord ++ tailWord_184029).sum := by decide
  have hdescent : baseEnd_184029 < baseStart_184029 := by decide
  rcases family_descends (prefixWord ++ tailWord_184029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184035 : List Nat := [1, 1, 1, 7, 2, 2, 2, 2, 2]
def baseStart_184035 : Nat := 118140960795 + 184035 * 2 ^ 59
def prefixEnd_184035 : Nat := 4983230072969 + 3 ^ 40 * 184035 * 2
def baseEnd_184035 : Nat := 83998588666926840814351

theorem tailTrace_184035 : CollatzResearch.WordTrace tailWord_184035 prefixEnd_184035 83998588666926840814351 := by
  unfold tailWord_184035
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712307888280100520785559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4474871925520067013857039 6712307888280100520785559)
  ·
    refine ⟨10068461832420150781178339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6712307888280100520785559 10068461832420150781178339)
    ·
      refine ⟨15102692748630226171767509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10068461832420150781178339 15102692748630226171767509)
      ·
        refine ⟨353969361296020925900801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 15102692748630226171767509 353969361296020925900801)
        ·
          refine ⟨265477020972015694425601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353969361296020925900801 265477020972015694425601)
          ·
            refine ⟨199107765729011770819201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265477020972015694425601 199107765729011770819201)
            ·
              refine ⟨149330824296758828114401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199107765729011770819201 149330824296758828114401)
              ·
                refine ⟨111998118222569121085801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149330824296758828114401 111998118222569121085801)
                ·
                  refine ⟨83998588666926840814351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111998118222569121085801 83998588666926840814351)
                  ·
                    rfl

theorem cell20_184035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 2].length) (baseStart_184035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184035 prefixEnd_184035 := by exact prefixLift 184035
  have htrace : WordTrace (prefixWord ++ tailWord_184035) baseStart_184035 baseEnd_184035 := by
    simpa [prefixWord, tailWord_184035, baseEnd_184035] using wordTrace_append hprefix tailTrace_184035
  have hstable : (prefixWord ++ tailWord_184035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184035).length < 2 ^ (prefixWord ++ tailWord_184035).sum := by decide
  have hdescent : baseEnd_184035 < baseStart_184035 := by decide
  rcases family_descends (prefixWord ++ tailWord_184035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184057 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_184057 : Nat := 118140960795 + 184057 * 2 ^ 59
def prefixEnd_184057 : Nat := 4983230072969 + 3 ^ 40 * 184057 * 2
def baseEnd_184057 : Nat := 84008630066392542080927

theorem tailTrace_184057 : CollatzResearch.WordTrace tailWord_184057 prefixEnd_184057 84008630066392542080927 := by
  unfold tailWord_184057
  simp only [CollatzResearch.WordTrace]
  refine ⟨6713110294200398278086425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4475406862800265518724283 6713110294200398278086425)
  ·
    refine ⟨5034832720650298708564819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6713110294200398278086425 5034832720650298708564819)
    ·
      refine ⟨7552249080975448062847229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5034832720650298708564819 7552249080975448062847229)
      ·
        refine ⟨2832093405365793023567711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7552249080975448062847229 2832093405365793023567711)
        ·
          refine ⟨4248140108048689535351567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832093405365793023567711 4248140108048689535351567)
          ·
            refine ⟨6372210162073034303027351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4248140108048689535351567 6372210162073034303027351)
            ·
              refine ⟨9558315243109551454541027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6372210162073034303027351 9558315243109551454541027)
              ·
                refine ⟨14337472864664327181811541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9558315243109551454541027 14337472864664327181811541)
                ·
                  refine ⟨84008630066392542080927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14337472864664327181811541 84008630066392542080927)
                  ·
                    rfl

theorem cell20_184057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_184057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184057 prefixEnd_184057 := by exact prefixLift 184057
  have htrace : WordTrace (prefixWord ++ tailWord_184057) baseStart_184057 baseEnd_184057 := by
    simpa [prefixWord, tailWord_184057, baseEnd_184057] using wordTrace_append hprefix tailTrace_184057
  have hstable : (prefixWord ++ tailWord_184057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184057).length < 2 ^ (prefixWord ++ tailWord_184057).sum := by decide
  have hdescent : baseEnd_184057 < baseStart_184057 := by decide
  rcases family_descends (prefixWord ++ tailWord_184057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184098 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_184098 : Nat := 118140960795 + 184098 * 2 ^ 59
def prefixEnd_184098 : Nat := 4983230072969 + 3 ^ 40 * 184098 * 2
def baseEnd_184098 : Nat := 84027343583578621714093

theorem tailTrace_184098 : CollatzResearch.WordTrace tailWord_184098 prefixEnd_184098 84027343583578621714093 := by
  unfold tailWord_184098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1678651421762965570082237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4476403791367908186885965 1678651421762965570082237)
  ·
    refine ⟨629494283161112088780839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1678651421762965570082237 629494283161112088780839)
    ·
      refine ⟨944241424741668133171259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 629494283161112088780839 944241424741668133171259)
      ·
        refine ⟨1416362137112502199756889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944241424741668133171259 1416362137112502199756889)
        ·
          refine ⟨1062271602834376649817667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1416362137112502199756889 1062271602834376649817667)
          ·
            refine ⟨1593407404251564974726501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062271602834376649817667 1593407404251564974726501)
            ·
              refine ⟨298763888297168432761219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1593407404251564974726501 298763888297168432761219)
              ·
                refine ⟨448145832445752649141829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298763888297168432761219 448145832445752649141829)
                ·
                  refine ⟨84027343583578621714093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 448145832445752649141829 84027343583578621714093)
                  ·
                    rfl

theorem cell20_184098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_184098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184098 prefixEnd_184098 := by exact prefixLift 184098
  have htrace : WordTrace (prefixWord ++ tailWord_184098) baseStart_184098 baseEnd_184098 := by
    simpa [prefixWord, tailWord_184098, baseEnd_184098] using wordTrace_append hprefix tailTrace_184098
  have hstable : (prefixWord ++ tailWord_184098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184098).length < 2 ^ (prefixWord ++ tailWord_184098).sum := by decide
  have hdescent : baseEnd_184098 < baseStart_184098 := by decide
  rcases family_descends (prefixWord ++ tailWord_184098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184122 : List Nat := [3, 1, 1, 1, 5, 3, 2, 4]
def baseStart_184122 : Nat := 118140960795 + 184122 * 2 ^ 59
def prefixEnd_184122 : Nat := 4983230072969 + 3 ^ 40 * 184122 * 2
def baseEnd_184122 : Nat := 28012765945847068304665

theorem tailTrace_184122 : CollatzResearch.WordTrace tailWord_184122 prefixEnd_184122 28012765945847068304665 := by
  unfold tailWord_184122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1678870259741228594800655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4476987359309942919468413 1678870259741228594800655)
  ·
    refine ⟨2518305389611842892200983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1678870259741228594800655 2518305389611842892200983)
    ·
      refine ⟨3777458084417764338301475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2518305389611842892200983 3777458084417764338301475)
      ·
        refine ⟨5666187126626646507452213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3777458084417764338301475 5666187126626646507452213)
        ·
          refine ⟨531205043121248110073645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5666187126626646507452213 531205043121248110073645)
          ·
            refine ⟨199201891170468041277617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 531205043121248110073645 199201891170468041277617)
            ·
              refine ⟨149401418377851030958213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199201891170468041277617 149401418377851030958213)
              ·
                refine ⟨28012765945847068304665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149401418377851030958213 28012765945847068304665)
                ·
                  rfl

theorem cell20_184122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_184122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184122 prefixEnd_184122 := by exact prefixLift 184122
  have htrace : WordTrace (prefixWord ++ tailWord_184122) baseStart_184122 baseEnd_184122 := by
    simpa [prefixWord, tailWord_184122, baseEnd_184122] using wordTrace_append hprefix tailTrace_184122
  have hstable : (prefixWord ++ tailWord_184122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184122).length < 2 ^ (prefixWord ++ tailWord_184122).sum := by decide
  have hdescent : baseEnd_184122 < baseStart_184122 := by decide
  rcases family_descends (prefixWord ++ tailWord_184122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184133 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_184133 : Nat := 118140960795 + 184133 * 2 ^ 59
def prefixEnd_184133 : Nat := 4983230072969 + 3 ^ 40 * 184133 * 2
def baseEnd_184133 : Nat := 84043318537274055547283

theorem tailTrace_184133 : CollatzResearch.WordTrace tailWord_184133 prefixEnd_184133 84043318537274055547283 := by
  unfold tailWord_184133
  simp only [CollatzResearch.WordTrace]
  refine ⟨6715882241925063257853053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4477254827950042171902035 6715882241925063257853053)
  ·
    refine ⟨2518455840721898721694895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6715882241925063257853053 2518455840721898721694895)
    ·
      refine ⟨3777683761082848082542343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2518455840721898721694895 3777683761082848082542343)
      ·
        refine ⟨5666525641624272123813515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3777683761082848082542343 5666525641624272123813515)
        ·
          refine ⟨8499788462436408185720273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5666525641624272123813515 8499788462436408185720273)
          ·
            refine ⟨6374841346827306139290205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8499788462436408185720273 6374841346827306139290205)
            ·
              refine ⟨2390565505060239802233827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6374841346827306139290205 2390565505060239802233827)
              ·
                refine ⟨3585848257590359703350741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390565505060239802233827 3585848257590359703350741)
                ·
                  refine ⟨84043318537274055547283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3585848257590359703350741 84043318537274055547283)
                  ·
                    rfl

theorem cell20_184133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_184133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184133 prefixEnd_184133 := by exact prefixLift 184133
  have htrace : WordTrace (prefixWord ++ tailWord_184133) baseStart_184133 baseEnd_184133 := by
    simpa [prefixWord, tailWord_184133, baseEnd_184133] using wordTrace_append hprefix tailTrace_184133
  have hstable : (prefixWord ++ tailWord_184133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184133).length < 2 ^ (prefixWord ++ tailWord_184133).sum := by decide
  have hdescent : baseEnd_184133 < baseStart_184133 := by decide
  rcases family_descends (prefixWord ++ tailWord_184133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184153 : List Nat := [1, 2, 1, 2, 2, 3, 5, 2, 2]
def baseStart_184153 : Nat := 118140960795 + 184153 * 2 ^ 59
def prefixEnd_184153 : Nat := 4983230072969 + 3 ^ 40 * 184153 * 2
def baseEnd_184153 : Nat := 84052447082242874880535

theorem tailTrace_184153 : CollatzResearch.WordTrace tailWord_184153 prefixEnd_184153 84052447082242874880535 := by
  unfold tailWord_184153
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716611701852606673581113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4477741134568404449054075 6716611701852606673581113)
  ·
    refine ⟨5037458776389455005185835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6716611701852606673581113 5037458776389455005185835)
    ·
      refine ⟨7556188164584182507778753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5037458776389455005185835 7556188164584182507778753)
      ·
        refine ⟨5667141123438136880834065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7556188164584182507778753 5667141123438136880834065)
        ·
          refine ⟨4250355842578602660625549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5667141123438136880834065 4250355842578602660625549)
          ·
            refine ⟨1593883440966975997734581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4250355842578602660625549 1593883440966975997734581)
            ·
              refine ⟨149426572590653999787617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1593883440966975997734581 149426572590653999787617)
              ·
                refine ⟨112069929442990499840713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149426572590653999787617 112069929442990499840713)
                ·
                  refine ⟨84052447082242874880535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112069929442990499840713 84052447082242874880535)
                  ·
                    rfl

theorem cell20_184153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 2].length) (baseStart_184153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184153 prefixEnd_184153 := by exact prefixLift 184153
  have htrace : WordTrace (prefixWord ++ tailWord_184153) baseStart_184153 baseEnd_184153 := by
    simpa [prefixWord, tailWord_184153, baseEnd_184153] using wordTrace_append hprefix tailTrace_184153
  have hstable : (prefixWord ++ tailWord_184153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184153).length < 2 ^ (prefixWord ++ tailWord_184153).sum := by decide
  have hdescent : baseEnd_184153 < baseStart_184153 := by decide
  rcases family_descends (prefixWord ++ tailWord_184153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184163 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 3]
def baseStart_184163 : Nat := 118140960795 + 184163 * 2 ^ 59
def prefixEnd_184163 : Nat := 4983230072969 + 3 ^ 40 * 184163 * 2
def baseEnd_184163 : Nat := 84057011354727284547161

theorem tailTrace_184163 : CollatzResearch.WordTrace tailWord_184163 prefixEnd_184163 84057011354727284547161 := by
  unfold tailWord_184163
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716976431816378381445143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4477984287877585587630095 6716976431816378381445143)
  ·
    refine ⟨10075464647724567572167715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6716976431816378381445143 10075464647724567572167715)
    ·
      refine ⟨15113196971586851358251573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10075464647724567572167715 15113196971586851358251573)
      ·
        refine ⟨1416862216086267314836085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15113196971586851358251573 1416862216086267314836085)
        ·
          refine ⟨132830832758087560765883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1416862216086267314836085 132830832758087560765883)
          ·
            refine ⟨199246249137131341148825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132830832758087560765883 199246249137131341148825)
            ·
              refine ⟨149434686852848505861619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199246249137131341148825 149434686852848505861619)
              ·
                refine ⟨224152030279272758792429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149434686852848505861619 224152030279272758792429)
                ·
                  refine ⟨84057011354727284547161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224152030279272758792429 84057011354727284547161)
                  ·
                    rfl

theorem cell20_184163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 3].length) (baseStart_184163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184163 prefixEnd_184163 := by exact prefixLift 184163
  have htrace : WordTrace (prefixWord ++ tailWord_184163) baseStart_184163 baseEnd_184163 := by
    simpa [prefixWord, tailWord_184163, baseEnd_184163] using wordTrace_append hprefix tailTrace_184163
  have hstable : (prefixWord ++ tailWord_184163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184163).length < 2 ^ (prefixWord ++ tailWord_184163).sum := by decide
  have hdescent : baseEnd_184163 < baseStart_184163 := by decide
  rcases family_descends (prefixWord ++ tailWord_184163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184202 : List Nat := [3, 1, 2, 4, 10]
def baseStart_184202 : Nat := 118140960795 + 184202 * 2 ^ 59
def prefixEnd_184202 : Nat := 4983230072969 + 3 ^ 40 * 184202 * 2
def baseEnd_184202 : Nat := 1037960642190326941321

theorem tailTrace_184202 : CollatzResearch.WordTrace tailWord_184202 prefixEnd_184202 1037960642190326941321 := by
  unfold tailWord_184202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1679599719668772010528715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4478932585783392028076573 1679599719668772010528715)
  ·
    refine ⟨2519399579503158015793073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1679599719668772010528715 2519399579503158015793073)
    ·
      refine ⟨1889549684627368511844805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2519399579503158015793073 1889549684627368511844805)
      ·
        refine ⟨354290565867631595970901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1889549684627368511844805 354290565867631595970901)
        ·
          refine ⟨1037960642190326941321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 354290565867631595970901 1037960642190326941321)
          ·
            rfl

theorem cell20_184202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 10].length) (baseStart_184202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184202 prefixEnd_184202 := by exact prefixLift 184202
  have htrace : WordTrace (prefixWord ++ tailWord_184202) baseStart_184202 baseEnd_184202 := by
    simpa [prefixWord, tailWord_184202, baseEnd_184202] using wordTrace_append hprefix tailTrace_184202
  have hstable : (prefixWord ++ tailWord_184202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184202).length < 2 ^ (prefixWord ++ tailWord_184202).sum := by decide
  have hdescent : baseEnd_184202 < baseStart_184202 := by decide
  rcases family_descends (prefixWord ++ tailWord_184202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184209 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_184209 : Nat := 118140960795 + 184209 * 2 ^ 59
def prefixEnd_184209 : Nat := 4983230072969 + 3 ^ 40 * 184209 * 2
def baseEnd_184209 : Nat := 84078007008155569013639

theorem tailTrace_184209 : CollatzResearch.WordTrace tailWord_184209 prefixEnd_184209 84078007008155569013639 := by
  unfold tailWord_184209
  simp only [CollatzResearch.WordTrace]
  refine ⟨6718654189649728237619681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4479102793099818825079787 6718654189649728237619681)
  ·
    refine ⟨5038990642237296178214761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6718654189649728237619681 5038990642237296178214761)
    ·
      refine ⟨3779242981677972133661071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5038990642237296178214761 3779242981677972133661071)
      ·
        refine ⟨5668864472516958200491607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779242981677972133661071 5668864472516958200491607)
        ·
          refine ⟨8503296708775437300737411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5668864472516958200491607 8503296708775437300737411)
          ·
            refine ⟨12754945063163155951106117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8503296708775437300737411 12754945063163155951106117)
            ·
              refine ⟨2391552199343091740832397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12754945063163155951106117 2391552199343091740832397)
              ·
                refine ⟨896832074753659402812149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2391552199343091740832397 896832074753659402812149)
                ·
                  refine ⟨84078007008155569013639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 896832074753659402812149 84078007008155569013639)
                  ·
                    rfl

theorem cell20_184209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_184209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184209 prefixEnd_184209 := by exact prefixLift 184209
  have htrace : WordTrace (prefixWord ++ tailWord_184209) baseStart_184209 baseEnd_184209 := by
    simpa [prefixWord, tailWord_184209, baseEnd_184209] using wordTrace_append hprefix tailTrace_184209
  have hstable : (prefixWord ++ tailWord_184209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184209).length < 2 ^ (prefixWord ++ tailWord_184209).sum := by decide
  have hdescent : baseEnd_184209 < baseStart_184209 := by decide
  rcases family_descends (prefixWord ++ tailWord_184209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184247 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_184247 : Nat := 118140960795 + 184247 * 2 ^ 59
def prefixEnd_184247 : Nat := 4983230072969 + 3 ^ 40 * 184247 * 2
def baseEnd_184247 : Nat := 84095351243596325746817

theorem tailTrace_184247 : CollatzResearch.WordTrace tailWord_184247 prefixEnd_184247 84095351243596325746817 := by
  unfold tailWord_184247
  simp only [CollatzResearch.WordTrace]
  refine ⟨6720040163512060727502995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4480026775674707151668663 6720040163512060727502995)
  ·
    refine ⟨10080060245268091091254493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6720040163512060727502995 10080060245268091091254493)
    ·
      refine ⟨3780022591975534159220435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10080060245268091091254493 3780022591975534159220435)
      ·
        refine ⟨5670033887963301238830653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3780022591975534159220435 5670033887963301238830653)
        ·
          refine ⟨2126262707986237964561495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5670033887963301238830653 2126262707986237964561495)
          ·
            refine ⟨3189394061979356946842243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126262707986237964561495 3189394061979356946842243)
            ·
              refine ⟨4784091092969035420263365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3189394061979356946842243 4784091092969035420263365)
              ·
                refine ⟨897017079931694141299381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4784091092969035420263365 897017079931694141299381)
                ·
                  refine ⟨84095351243596325746817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 897017079931694141299381 84095351243596325746817)
                  ·
                    rfl

theorem cell20_184247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_184247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184247 prefixEnd_184247 := by exact prefixLift 184247
  have htrace : WordTrace (prefixWord ++ tailWord_184247) baseStart_184247 baseEnd_184247 := by
    simpa [prefixWord, tailWord_184247, baseEnd_184247] using wordTrace_append hprefix tailTrace_184247
  have hstable : (prefixWord ++ tailWord_184247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184247).length < 2 ^ (prefixWord ++ tailWord_184247).sum := by decide
  have hdescent : baseEnd_184247 < baseStart_184247 := by decide
  rcases family_descends (prefixWord ++ tailWord_184247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184264 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_184264 : Nat := 118140960795 + 184264 * 2 ^ 59
def prefixEnd_184264 : Nat := 4983230072969 + 3 ^ 40 * 184264 * 2
def baseEnd_184264 : Nat := 84103110506819822180081

theorem tailTrace_184264 : CollatzResearch.WordTrace tailWord_184264 prefixEnd_184264 84103110506819822180081 := by
  unfold tailWord_184264
  simp only [CollatzResearch.WordTrace]
  refine ⟨3360330102225236315435923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4480440136300315087247897 3360330102225236315435923)
  ·
    refine ⟨5040495153337854473153885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3360330102225236315435923 5040495153337854473153885)
    ·
      refine ⟨1890185682501695427432707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5040495153337854473153885 1890185682501695427432707)
      ·
        refine ⟨2835278523752543141149061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890185682501695427432707 2835278523752543141149061)
        ·
          refine ⟨531614723203601838965449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2835278523752543141149061 531614723203601838965449)
          ·
            refine ⟨398711042402701379224087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531614723203601838965449 398711042402701379224087)
            ·
              refine ⟨598066563604052068836131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398711042402701379224087 598066563604052068836131)
              ·
                refine ⟨897099845406078103254197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598066563604052068836131 897099845406078103254197)
                ·
                  refine ⟨84103110506819822180081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 897099845406078103254197 84103110506819822180081)
                  ·
                    rfl

theorem cell20_184264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_184264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184264 prefixEnd_184264 := by exact prefixLift 184264
  have htrace : WordTrace (prefixWord ++ tailWord_184264) baseStart_184264 baseEnd_184264 := by
    simpa [prefixWord, tailWord_184264, baseEnd_184264] using wordTrace_append hprefix tailTrace_184264
  have hstable : (prefixWord ++ tailWord_184264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184264).length < 2 ^ (prefixWord ++ tailWord_184264).sum := by decide
  have hdescent : baseEnd_184264 < baseStart_184264 := by decide
  rcases family_descends (prefixWord ++ tailWord_184264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184271 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 4]
def baseStart_184271 : Nat := 118140960795 + 184271 * 2 ^ 59
def prefixEnd_184271 : Nat := 4983230072969 + 3 ^ 40 * 184271 * 2
def baseEnd_184271 : Nat := 84106305497558908946719

theorem tailTrace_184271 : CollatzResearch.WordTrace tailWord_184271 prefixEnd_184271 84106305497558908946719 := by
  unfold tailWord_184271
  simp only [CollatzResearch.WordTrace]
  refine ⟨6720915515425112826376667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4480610343616741884251111 6720915515425112826376667)
  ·
    refine ⟨10081373273137669239565001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6720915515425112826376667 10081373273137669239565001)
    ·
      refine ⟨7561029954853251929673751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10081373273137669239565001 7561029954853251929673751)
      ·
        refine ⟨11341544932279877894510627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7561029954853251929673751 11341544932279877894510627)
        ·
          refine ⟨17012317398419816841765941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11341544932279877894510627 17012317398419816841765941)
          ·
            refine ⟨1594904756101857828915557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17012317398419816841765941 1594904756101857828915557)
            ·
              refine ⟨299044641769098342921667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1594904756101857828915557 299044641769098342921667)
              ·
                refine ⟨448566962653647514382501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299044641769098342921667 448566962653647514382501)
                ·
                  refine ⟨84106305497558908946719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 448566962653647514382501 84106305497558908946719)
                  ·
                    rfl

theorem cell20_184271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_184271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184271 prefixEnd_184271 := by exact prefixLift 184271
  have htrace : WordTrace (prefixWord ++ tailWord_184271) baseStart_184271 baseEnd_184271 := by
    simpa [prefixWord, tailWord_184271, baseEnd_184271] using wordTrace_append hprefix tailTrace_184271
  have hstable : (prefixWord ++ tailWord_184271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184271).length < 2 ^ (prefixWord ++ tailWord_184271).sum := by decide
  have hdescent : baseEnd_184271 < baseStart_184271 := by decide
  rcases family_descends (prefixWord ++ tailWord_184271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184295 : List Nat := [1, 1, 5, 2, 3, 1, 1, 6]
def baseStart_184295 : Nat := 118140960795 + 184295 * 2 ^ 59
def prefixEnd_184295 : Nat := 4983230072969 + 3 ^ 40 * 184295 * 2
def baseEnd_184295 : Nat := 28039086583840497382207

theorem tailTrace_184295 : CollatzResearch.WordTrace tailWord_184295 prefixEnd_184295 28039086583840497382207 := by
  unfold tailWord_184295
  simp only [CollatzResearch.WordTrace]
  refine ⟨6721790867338164925250339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4481193911558776616833559 6721790867338164925250339)
  ·
    refine ⟨10082686301007247387875509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6721790867338164925250339 10082686301007247387875509)
    ·
      refine ⟨945251840719429442613329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10082686301007247387875509 945251840719429442613329)
      ·
        refine ⟨708938880539572081959997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 945251840719429442613329 708938880539572081959997)
        ·
          refine ⟨265852080202339530734999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 708938880539572081959997 265852080202339530734999)
          ·
            refine ⟨398778120303509296102499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265852080202339530734999 398778120303509296102499)
            ·
              refine ⟨598167180455263944153749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398778120303509296102499 598167180455263944153749)
              ·
                refine ⟨28039086583840497382207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 598167180455263944153749 28039086583840497382207)
                ·
                  rfl

theorem cell20_184295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 6].length) (baseStart_184295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184295 prefixEnd_184295 := by exact prefixLift 184295
  have htrace : WordTrace (prefixWord ++ tailWord_184295) baseStart_184295 baseEnd_184295 := by
    simpa [prefixWord, tailWord_184295, baseEnd_184295] using wordTrace_append hprefix tailTrace_184295
  have hstable : (prefixWord ++ tailWord_184295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184295).length < 2 ^ (prefixWord ++ tailWord_184295).sum := by decide
  have hdescent : baseEnd_184295 < baseStart_184295 := by decide
  rcases family_descends (prefixWord ++ tailWord_184295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184301 : List Nat := [1, 5, 1, 4, 1, 2, 1, 3, 2]
def baseStart_184301 : Nat := 118140960795 + 184301 * 2 ^ 59
def prefixEnd_184301 : Nat := 4983230072969 + 3 ^ 40 * 184301 * 2
def baseEnd_184301 : Nat := 84119998315012137946597

theorem tailTrace_184301 : CollatzResearch.WordTrace tailWord_184301 prefixEnd_184301 84119998315012137946597 := by
  unfold tailWord_184301
  simp only [CollatzResearch.WordTrace]
  refine ⟨6722009705316427949968757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4481339803544285299979171 6722009705316427949968757)
  ·
    refine ⟨630188409873415120309571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6722009705316427949968757 630188409873415120309571)
    ·
      refine ⟨945282614810122680464357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 630188409873415120309571 945282614810122680464357)
      ·
        refine ⟨177240490276898002587067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 945282614810122680464357 177240490276898002587067)
        ·
          refine ⟨265860735415347003880601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177240490276898002587067 265860735415347003880601)
          ·
            refine ⟨199395551561510252910451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265860735415347003880601 199395551561510252910451)
            ·
              refine ⟨299093327342265379365677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199395551561510252910451 299093327342265379365677)
              ·
                refine ⟨112159997753349517262129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299093327342265379365677 112159997753349517262129)
                ·
                  refine ⟨84119998315012137946597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112159997753349517262129 84119998315012137946597)
                  ·
                    rfl

theorem cell20_184301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_184301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184301 prefixEnd_184301 := by exact prefixLift 184301
  have htrace : WordTrace (prefixWord ++ tailWord_184301) baseStart_184301 baseEnd_184301 := by
    simpa [prefixWord, tailWord_184301, baseEnd_184301] using wordTrace_append hprefix tailTrace_184301
  have hstable : (prefixWord ++ tailWord_184301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184301).length < 2 ^ (prefixWord ++ tailWord_184301).sum := by decide
  have hdescent : baseEnd_184301 < baseStart_184301 := by decide
  rcases family_descends (prefixWord ++ tailWord_184301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184302 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_184302 : Nat := 118140960795 + 184302 * 2 ^ 59
def prefixEnd_184302 : Nat := 4983230072969 + 3 ^ 40 * 184302 * 2
def baseEnd_184302 : Nat := 84120454742260578913259

theorem tailTrace_184302 : CollatzResearch.WordTrace tailWord_184302 prefixEnd_184302 84120454742260578913259 := by
  unfold tailWord_184302
  simp only [CollatzResearch.WordTrace]
  refine ⟨840255772289100640094395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4481364118875203413836773 840255772289100640094395)
  ·
    refine ⟨1260383658433650960141593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 840255772289100640094395 1260383658433650960141593)
    ·
      refine ⟨945287743825238220106195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1260383658433650960141593 945287743825238220106195)
      ·
        refine ⟨1417931615737857330159293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945287743825238220106195 1417931615737857330159293)
        ·
          refine ⟨531724355901696498809735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1417931615737857330159293 531724355901696498809735)
          ·
            refine ⟨797586533852544748214603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531724355901696498809735 797586533852544748214603)
            ·
              refine ⟨1196379800778817122321905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797586533852544748214603 1196379800778817122321905)
              ·
                refine ⟨897284850584112841741429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196379800778817122321905 897284850584112841741429)
                ·
                  refine ⟨84120454742260578913259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 897284850584112841741429 84120454742260578913259)
                  ·
                    rfl

theorem cell20_184302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_184302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184302 prefixEnd_184302 := by exact prefixLift 184302
  have htrace : WordTrace (prefixWord ++ tailWord_184302) baseStart_184302 baseEnd_184302 := by
    simpa [prefixWord, tailWord_184302, baseEnd_184302] using wordTrace_append hprefix tailTrace_184302
  have hstable : (prefixWord ++ tailWord_184302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184302).length < 2 ^ (prefixWord ++ tailWord_184302).sum := by decide
  have hdescent : baseEnd_184302 < baseStart_184302 := by decide
  rcases family_descends (prefixWord ++ tailWord_184302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184354 : List Nat := [3, 3, 1, 1, 1, 2, 1, 8]
def baseStart_184354 : Nat := 118140960795 + 184354 * 2 ^ 59
def prefixEnd_184354 : Nat := 4983230072969 + 3 ^ 40 * 184354 * 2
def baseEnd_184354 : Nat := 28048062986393169726571

theorem tailTrace_184354 : CollatzResearch.WordTrace tailWord_184354 prefixEnd_184354 28048062986393169726571 := by
  unfold tailWord_184354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1680985693531104500412029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4482628516082945334432077 1680985693531104500412029)
  ·
    refine ⟨630369635074164187654511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1680985693531104500412029 630369635074164187654511)
    ·
      refine ⟨945554452611246281481767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 630369635074164187654511 945554452611246281481767)
      ·
        refine ⟨1418331678916869422222651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945554452611246281481767 1418331678916869422222651)
        ·
          refine ⟨2127497518375304133333977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418331678916869422222651 2127497518375304133333977)
          ·
            refine ⟨1595623138781478100000483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2127497518375304133333977 1595623138781478100000483)
            ·
              refine ⟨2393434708172217150000725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595623138781478100000483 2393434708172217150000725)
              ·
                refine ⟨28048062986393169726571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2393434708172217150000725 28048062986393169726571)
                ·
                  rfl

theorem cell20_184354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_184354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184354 prefixEnd_184354 := by exact prefixLift 184354
  have htrace : WordTrace (prefixWord ++ tailWord_184354) baseStart_184354 baseEnd_184354 := by
    simpa [prefixWord, tailWord_184354, baseEnd_184354] using wordTrace_append hprefix tailTrace_184354
  have hstable : (prefixWord ++ tailWord_184354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184354).length < 2 ^ (prefixWord ++ tailWord_184354).sum := by decide
  have hdescent : baseEnd_184354 < baseStart_184354 := by decide
  rcases family_descends (prefixWord ++ tailWord_184354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184377 : List Nat := [1, 2, 1, 5, 4, 1, 2, 2, 2]
def baseStart_184377 : Nat := 118140960795 + 184377 * 2 ^ 59
def prefixEnd_184377 : Nat := 4983230072969 + 3 ^ 40 * 184377 * 2
def baseEnd_184377 : Nat := 84154686785893651412953

theorem tailTrace_184377 : CollatzResearch.WordTrace tailWord_184377 prefixEnd_184377 84154686785893651412953 := by
  unfold tailWord_184377
  simp only [CollatzResearch.WordTrace]
  refine ⟨6724781653041092929735385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4483187768694061953156923 6724781653041092929735385)
  ·
    refine ⟨5043586239780819697301539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6724781653041092929735385 5043586239780819697301539)
    ·
      refine ⟨7565379359671229545952309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5043586239780819697301539 7565379359671229545952309)
      ·
        refine ⟨709254314969177769933029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7565379359671229545952309 709254314969177769933029)
        ·
          refine ⟨132985184056720831862443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 709254314969177769933029 132985184056720831862443)
          ·
            refine ⟨199477776085081247793665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132985184056720831862443 199477776085081247793665)
            ·
              refine ⟨149608332063810935845249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199477776085081247793665 149608332063810935845249)
              ·
                refine ⟨112206249047858201883937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149608332063810935845249 112206249047858201883937)
                ·
                  refine ⟨84154686785893651412953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112206249047858201883937 84154686785893651412953)
                  ·
                    rfl

theorem cell20_184377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 2].length) (baseStart_184377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184377 prefixEnd_184377 := by exact prefixLift 184377
  have htrace : WordTrace (prefixWord ++ tailWord_184377) baseStart_184377 baseEnd_184377 := by
    simpa [prefixWord, tailWord_184377, baseEnd_184377] using wordTrace_append hprefix tailTrace_184377
  have hstable : (prefixWord ++ tailWord_184377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184377).length < 2 ^ (prefixWord ++ tailWord_184377).sum := by decide
  have hdescent : baseEnd_184377 < baseStart_184377 := by decide
  rcases family_descends (prefixWord ++ tailWord_184377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184402 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_184402 : Nat := 118140960795 + 184402 * 2 ^ 59
def prefixEnd_184402 : Nat := 4983230072969 + 3 ^ 40 * 184402 * 2
def baseEnd_184402 : Nat := 84166097467104675579517

theorem tailTrace_184402 : CollatzResearch.WordTrace tailWord_184402 prefixEnd_184402 84166097467104675579517 := by
  unfold tailWord_184402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1681423369487630549848865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4483795651967014799596973 1681423369487630549848865)
  ·
    refine ⟨1261067527115722912386649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1681423369487630549848865 1261067527115722912386649)
    ·
      refine ⟨945800645336792184289987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1261067527115722912386649 945800645336792184289987)
      ·
        refine ⟨1418700968005188276434981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945800645336792184289987 1418700968005188276434981)
        ·
          refine ⟨266006431500972801831559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1418700968005188276434981 266006431500972801831559)
          ·
            refine ⟨399009647251459202747339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266006431500972801831559 399009647251459202747339)
            ·
              refine ⟨598514470877188804121009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399009647251459202747339 598514470877188804121009)
              ·
                refine ⟨448885853157891603090757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598514470877188804121009 448885853157891603090757)
                ·
                  refine ⟨84166097467104675579517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 448885853157891603090757 84166097467104675579517)
                  ·
                    rfl

theorem cell20_184402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_184402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184402 prefixEnd_184402 := by exact prefixLift 184402
  have htrace : WordTrace (prefixWord ++ tailWord_184402) baseStart_184402 baseEnd_184402 := by
    simpa [prefixWord, tailWord_184402, baseEnd_184402] using wordTrace_append hprefix tailTrace_184402
  have hstable : (prefixWord ++ tailWord_184402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184402).length < 2 ^ (prefixWord ++ tailWord_184402).sum := by decide
  have hdescent : baseEnd_184402 < baseStart_184402 := by decide
  rcases family_descends (prefixWord ++ tailWord_184402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184430 : List Nat := [4, 1, 2, 2, 1, 1, 9]
def baseStart_184430 : Nat := 118140960795 + 184430 * 2 ^ 59
def prefixEnd_184430 : Nat := 4983230072969 + 3 ^ 40 * 184430 * 2
def baseEnd_184430 : Nat := 9353208603340113627341

theorem tailTrace_184430 : CollatzResearch.WordTrace tailWord_184430 prefixEnd_184430 9353208603340113627341 := by
  unfold tailWord_184430
  simp only [CollatzResearch.WordTrace]
  refine ⟨840839340231135372676843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4484476481232721987609829 840839340231135372676843)
  ·
    refine ⟨1261259010346703059015265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 840839340231135372676843 1261259010346703059015265)
    ·
      refine ⟨945944257760027294261449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1261259010346703059015265 945944257760027294261449)
      ·
        refine ⟨709458193320020470696087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 945944257760027294261449 709458193320020470696087)
        ·
          refine ⟨1064187289980030706044131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709458193320020470696087 1064187289980030706044131)
          ·
            refine ⟨1596280934970046059066197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064187289980030706044131 1596280934970046059066197)
            ·
              refine ⟨9353208603340113627341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1596280934970046059066197 9353208603340113627341)
              ·
                rfl

theorem cell20_184430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 9].length) (baseStart_184430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184430 prefixEnd_184430 := by exact prefixLift 184430
  have htrace : WordTrace (prefixWord ++ tailWord_184430) baseStart_184430 baseEnd_184430 := by
    simpa [prefixWord, tailWord_184430, baseEnd_184430] using wordTrace_append hprefix tailTrace_184430
  have hstable : (prefixWord ++ tailWord_184430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184430).length < 2 ^ (prefixWord ++ tailWord_184430).sum := by decide
  have hdescent : baseEnd_184430 < baseStart_184430 := by decide
  rcases family_descends (prefixWord ++ tailWord_184430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184474 : List Nat := [3, 1, 1, 5, 2, 2, 1, 3, 2]
def baseStart_184474 : Nat := 118140960795 + 184474 * 2 ^ 59
def prefixEnd_184474 : Nat := 4983230072969 + 3 ^ 40 * 184474 * 2
def baseEnd_184474 : Nat := 84198960228992425179223

theorem tailTrace_184474 : CollatzResearch.WordTrace tailWord_184474 prefixEnd_184474 84198960228992425179223 := by
  unfold tailWord_184474
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682079883422419624004119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4485546355793118997344317 1682079883422419624004119)
  ·
    refine ⟨2523119825133629436006179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1682079883422419624004119 2523119825133629436006179)
    ·
      refine ⟨3784679737700444154009269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2523119825133629436006179 3784679737700444154009269)
      ·
        refine ⟨354813725409416639438369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3784679737700444154009269 354813725409416639438369)
        ·
          refine ⟨266110294057062479578777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354813725409416639438369 266110294057062479578777)
          ·
            refine ⟨199582720542796859684083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266110294057062479578777 199582720542796859684083)
            ·
              refine ⟨299374080814195289526125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199582720542796859684083 299374080814195289526125)
              ·
                refine ⟨112265280305323233572297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299374080814195289526125 112265280305323233572297)
                ·
                  refine ⟨84198960228992425179223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112265280305323233572297 84198960228992425179223)
                  ·
                    rfl

theorem cell20_184474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_184474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184474 prefixEnd_184474 := by exact prefixLift 184474
  have htrace : WordTrace (prefixWord ++ tailWord_184474) baseStart_184474 baseEnd_184474 := by
    simpa [prefixWord, tailWord_184474, baseEnd_184474] using wordTrace_append hprefix tailTrace_184474
  have hstable : (prefixWord ++ tailWord_184474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184474).length < 2 ^ (prefixWord ++ tailWord_184474).sum := by decide
  have hdescent : baseEnd_184474 < baseStart_184474 := by decide
  rcases family_descends (prefixWord ++ tailWord_184474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184520 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_184520 : Nat := 118140960795 + 184520 * 2 ^ 59
def prefixEnd_184520 : Nat := 4983230072969 + 3 ^ 40 * 184520 * 2
def baseEnd_184520 : Nat := 84219955882420709645701

theorem tailTrace_184520 : CollatzResearch.WordTrace tailWord_184520 prefixEnd_184520 84219955882420709645701 := by
  unfold tailWord_184520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3364998645761514176095507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4486664861015352234794009 3364998645761514176095507)
  ·
    refine ⟨5047497968642271264143261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3364998645761514176095507 5047497968642271264143261)
    ·
      refine ⟨1892811738240851724053723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5047497968642271264143261 1892811738240851724053723)
      ·
        refine ⟨2839217607361277586080585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892811738240851724053723 2839217607361277586080585)
        ·
          refine ⟨2129413205520958189560439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2839217607361277586080585 2129413205520958189560439)
          ·
            refine ⟨3194119808281437284340659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129413205520958189560439 3194119808281437284340659)
            ·
              refine ⟨4791179712422155926510989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194119808281437284340659 4791179712422155926510989)
              ·
                refine ⟨1796692392158308472441621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4791179712422155926510989 1796692392158308472441621)
                ·
                  refine ⟨84219955882420709645701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1796692392158308472441621 84219955882420709645701)
                  ·
                    rfl

theorem cell20_184520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_184520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184520 prefixEnd_184520 := by exact prefixLift 184520
  have htrace : WordTrace (prefixWord ++ tailWord_184520) baseStart_184520 baseEnd_184520 := by
    simpa [prefixWord, tailWord_184520, baseEnd_184520] using wordTrace_append hprefix tailTrace_184520
  have hstable : (prefixWord ++ tailWord_184520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184520).length < 2 ^ (prefixWord ++ tailWord_184520).sum := by decide
  have hdescent : baseEnd_184520 < baseStart_184520 := by decide
  rcases family_descends (prefixWord ++ tailWord_184520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184527 : List Nat := [1, 1, 2, 1, 1, 3, 3, 8]
def baseStart_184527 : Nat := 118140960795 + 184527 * 2 ^ 59
def prefixEnd_184527 : Nat := 4983230072969 + 3 ^ 40 * 184527 * 2
def baseEnd_184527 : Nat := 28074383624386598804113

theorem tailTrace_184527 : CollatzResearch.WordTrace tailWord_184527 prefixEnd_184527 28074383624386598804113 := by
  unfold tailWord_184527
  simp only [CollatzResearch.WordTrace]
  refine ⟨6730252602497668547695835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4486835068331779031797223 6730252602497668547695835)
  ·
    refine ⟨10095378903746502821543753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6730252602497668547695835 10095378903746502821543753)
    ·
      refine ⟨7571534177809877116157815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10095378903746502821543753 7571534177809877116157815)
      ·
        refine ⟨11357301266714815674236723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7571534177809877116157815 11357301266714815674236723)
        ·
          refine ⟨17035951900072223511355085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11357301266714815674236723 17035951900072223511355085)
          ·
            refine ⟨6388481962527083816758157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17035951900072223511355085 6388481962527083816758157)
            ·
              refine ⟨2395680735947656431284309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6388481962527083816758157 2395680735947656431284309)
              ·
                refine ⟨28074383624386598804113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2395680735947656431284309 28074383624386598804113)
                ·
                  rfl

theorem cell20_184527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_184527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184527 prefixEnd_184527 := by exact prefixLift 184527
  have htrace : WordTrace (prefixWord ++ tailWord_184527) baseStart_184527 baseEnd_184527 := by
    simpa [prefixWord, tailWord_184527, baseEnd_184527] using wordTrace_append hprefix tailTrace_184527
  have hstable : (prefixWord ++ tailWord_184527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184527).length < 2 ^ (prefixWord ++ tailWord_184527).sum := by decide
  have hdescent : baseEnd_184527 < baseStart_184527 := by decide
  rcases family_descends (prefixWord ++ tailWord_184527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184540 : List Nat := [2, 2, 5, 2, 2, 7]
def baseStart_184540 : Nat := 118140960795 + 184540 * 2 ^ 59
def prefixEnd_184540 : Nat := 4983230072969 + 3 ^ 40 * 184540 * 2
def baseEnd_184540 : Nat := 3119595719532945517739

theorem tailTrace_184540 : CollatzResearch.WordTrace tailWord_184540 prefixEnd_184540 3119595719532945517739 := by
  unfold tailWord_184540
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365363375725285883959537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4487151167633714511946049 3365363375725285883959537)
  ·
    refine ⟨2524022531793964412969653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3365363375725285883959537 2524022531793964412969653)
    ·
      refine ⟨236627112355684163715905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2524022531793964412969653 236627112355684163715905)
      ·
        refine ⟨177470334266763122786929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236627112355684163715905 177470334266763122786929)
        ·
          refine ⟨133102750700072342090197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177470334266763122786929 133102750700072342090197)
          ·
            refine ⟨3119595719532945517739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 133102750700072342090197 3119595719532945517739)
            ·
              rfl

theorem cell20_184540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 7].length) (baseStart_184540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184540 prefixEnd_184540 := by exact prefixLift 184540
  have htrace : WordTrace (prefixWord ++ tailWord_184540) baseStart_184540 baseEnd_184540 := by
    simpa [prefixWord, tailWord_184540, baseEnd_184540] using wordTrace_append hprefix tailTrace_184540
  have hstable : (prefixWord ++ tailWord_184540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184540).length < 2 ^ (prefixWord ++ tailWord_184540).sum := by decide
  have hdescent : baseEnd_184540 < baseStart_184540 := by decide
  rcases family_descends (prefixWord ++ tailWord_184540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184554 : List Nat := [3, 1, 3, 1, 1, 2, 3, 4, 2]
def baseStart_184554 : Nat := 118140960795 + 184554 * 2 ^ 59
def prefixEnd_184554 : Nat := 4983230072969 + 3 ^ 40 * 184554 * 2
def baseEnd_184554 : Nat := 84235474408867702512229

theorem tailTrace_184554 : CollatzResearch.WordTrace tailWord_184554 prefixEnd_184554 84235474408867702512229 := by
  unfold tailWord_184554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682809343349963039732179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4487491582266568105952477 1682809343349963039732179)
  ·
    refine ⟨2524214015024944559598269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1682809343349963039732179 2524214015024944559598269)
    ·
      refine ⟨946580255634354209849351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2524214015024944559598269 946580255634354209849351)
      ·
        refine ⟨1419870383451531314774027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946580255634354209849351 1419870383451531314774027)
        ·
          refine ⟨2129805575177296972161041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419870383451531314774027 2129805575177296972161041)
          ·
            refine ⟨1597354181382972729120781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2129805575177296972161041 1597354181382972729120781)
            ·
              refine ⟨599007818018614773420293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1597354181382972729120781 599007818018614773420293)
              ·
                refine ⟨112313965878490270016305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 599007818018614773420293 112313965878490270016305)
                ·
                  refine ⟨84235474408867702512229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112313965878490270016305 84235474408867702512229)
                  ·
                    rfl

theorem cell20_184554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_184554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184554 prefixEnd_184554 := by exact prefixLift 184554
  have htrace : WordTrace (prefixWord ++ tailWord_184554) baseStart_184554 baseEnd_184554 := by
    simpa [prefixWord, tailWord_184554, baseEnd_184554] using wordTrace_append hprefix tailTrace_184554
  have hstable : (prefixWord ++ tailWord_184554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184554).length < 2 ^ (prefixWord ++ tailWord_184554).sum := by decide
  have hdescent : baseEnd_184554 < baseStart_184554 := by decide
  rcases family_descends (prefixWord ++ tailWord_184554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184578 : List Nat := [3, 4, 1, 1, 2, 2, 3, 4]
def baseStart_184578 : Nat := 118140960795 + 184578 * 2 ^ 59
def prefixEnd_184578 : Nat := 4983230072969 + 3 ^ 40 * 184578 * 2
def baseEnd_184578 : Nat := 28082142887610095237377

theorem tailTrace_184578 : CollatzResearch.WordTrace tailWord_184578 prefixEnd_184578 28082142887610095237377 := by
  unfold tailWord_184578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1683028181328226064450597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4488075150208602838534925 1683028181328226064450597)
  ·
    refine ⟨315567783999042387084487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1683028181328226064450597 315567783999042387084487)
    ·
      refine ⟨473351675998563580626731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315567783999042387084487 473351675998563580626731)
      ·
        refine ⟨710027513997845370940097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473351675998563580626731 710027513997845370940097)
        ·
          refine ⟨532520635498384028205073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710027513997845370940097 532520635498384028205073)
          ·
            refine ⟨399390476623788021153805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532520635498384028205073 399390476623788021153805)
            ·
              refine ⟨149771428733920507932677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399390476623788021153805 149771428733920507932677)
              ·
                refine ⟨28082142887610095237377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149771428733920507932677 28082142887610095237377)
                ·
                  rfl

theorem cell20_184578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_184578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184578 prefixEnd_184578 := by exact prefixLift 184578
  have htrace : WordTrace (prefixWord ++ tailWord_184578) baseStart_184578 baseEnd_184578 := by
    simpa [prefixWord, tailWord_184578, baseEnd_184578] using wordTrace_append hprefix tailTrace_184578
  have hstable : (prefixWord ++ tailWord_184578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184578).length < 2 ^ (prefixWord ++ tailWord_184578).sum := by decide
  have hdescent : baseEnd_184578 < baseStart_184578 := by decide
  rcases family_descends (prefixWord ++ tailWord_184578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184602 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 3]
def baseStart_184602 : Nat := 118140960795 + 184602 * 2 ^ 59
def prefixEnd_184602 : Nat := 4983230072969 + 3 ^ 40 * 184602 * 2
def baseEnd_184602 : Nat := 84257382916792868912033

theorem tailTrace_184602 : CollatzResearch.WordTrace tailWord_184602 prefixEnd_184602 84257382916792868912033 := by
  unfold tailWord_184602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1683247019306489089169015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4488658718150637571117373 1683247019306489089169015)
  ·
    refine ⟨2524870528959733633753523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1683247019306489089169015 2524870528959733633753523)
    ·
      refine ⟨3787305793439600450630285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2524870528959733633753523 3787305793439600450630285)
      ·
        refine ⟨1420239672539850168986357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3787305793439600450630285 1420239672539850168986357)
        ·
          refine ⟨133147469300610953342471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1420239672539850168986357 133147469300610953342471)
          ·
            refine ⟨199721203950916430013707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133147469300610953342471 199721203950916430013707)
            ·
              refine ⟨299581805926374645020561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199721203950916430013707 299581805926374645020561)
              ·
                refine ⟨224686354444780983765421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299581805926374645020561 224686354444780983765421)
                ·
                  refine ⟨84257382916792868912033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224686354444780983765421 84257382916792868912033)
                  ·
                    rfl

theorem cell20_184602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_184602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184602 prefixEnd_184602 := by exact prefixLift 184602
  have htrace : WordTrace (prefixWord ++ tailWord_184602) baseStart_184602 baseEnd_184602 := by
    simpa [prefixWord, tailWord_184602, baseEnd_184602] using wordTrace_append hprefix tailTrace_184602
  have hstable : (prefixWord ++ tailWord_184602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184602).length < 2 ^ (prefixWord ++ tailWord_184602).sum := by decide
  have hdescent : baseEnd_184602 < baseStart_184602 := by decide
  rcases family_descends (prefixWord ++ tailWord_184602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184651 : List Nat := [1, 1, 1, 1, 3, 1, 1, 9, 2]
def baseStart_184651 : Nat := 118140960795 + 184651 * 2 ^ 59
def prefixEnd_184651 : Nat := 4983230072969 + 3 ^ 40 * 184651 * 2
def baseEnd_184651 : Nat := 84279747851966476278499

theorem tailTrace_184651 : CollatzResearch.WordTrace tailWord_184651 prefixEnd_184651 84279747851966476278499 := by
  unfold tailWord_184651
  simp only [CollatzResearch.WordTrace]
  refine ⟨6734775254048437725209807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4489850169365625150139871 6734775254048437725209807)
  ·
    refine ⟨10102162881072656587814711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6734775254048437725209807 10102162881072656587814711)
    ·
      refine ⟨15153244321608984881722067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10102162881072656587814711 15153244321608984881722067)
      ·
        refine ⟨22729866482413477322583101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15153244321608984881722067 22729866482413477322583101)
        ·
          refine ⟨8523699930905053995968663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22729866482413477322583101 8523699930905053995968663)
          ·
            refine ⟨12785549896357580993952995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8523699930905053995968663 12785549896357580993952995)
            ·
              refine ⟨19178324844536371490929493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12785549896357580993952995 19178324844536371490929493)
              ·
                refine ⟨112372997135955301704665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19178324844536371490929493 112372997135955301704665)
                ·
                  refine ⟨84279747851966476278499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112372997135955301704665 84279747851966476278499)
                  ·
                    rfl

theorem cell20_184651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 2].length) (baseStart_184651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184651 prefixEnd_184651 := by exact prefixLift 184651
  have htrace : WordTrace (prefixWord ++ tailWord_184651) baseStart_184651 baseEnd_184651 := by
    simpa [prefixWord, tailWord_184651, baseEnd_184651] using wordTrace_append hprefix tailTrace_184651
  have hstable : (prefixWord ++ tailWord_184651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184651).length < 2 ^ (prefixWord ++ tailWord_184651).sum := by decide
  have hdescent : baseEnd_184651 < baseStart_184651 := by decide
  rcases family_descends (prefixWord ++ tailWord_184651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184665 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 3]
def baseStart_184665 : Nat := 118140960795 + 184665 * 2 ^ 59
def prefixEnd_184665 : Nat := 4983230072969 + 3 ^ 40 * 184665 * 2
def baseEnd_184665 : Nat := 84286137833444649811775

theorem tailTrace_184665 : CollatzResearch.WordTrace tailWord_184665 prefixEnd_184665 84286137833444649811775 := by
  unfold tailWord_184665
  simp only [CollatzResearch.WordTrace]
  refine ⟨6735285875997718116219449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4490190583998478744146299 6735285875997718116219449)
  ·
    refine ⟨5051464406998288587164587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6735285875997718116219449 5051464406998288587164587)
    ·
      refine ⟨7577196610497432880746881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5051464406998288587164587 7577196610497432880746881)
      ·
        refine ⟨5682897457873074660560161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7577196610497432880746881 5682897457873074660560161)
        ·
          refine ⟨4262173093404805995420121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5682897457873074660560161 4262173093404805995420121)
          ·
            refine ⟨3196629820053604496565091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4262173093404805995420121 3196629820053604496565091)
            ·
              refine ⟨4794944730080406744847637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196629820053604496565091 4794944730080406744847637)
              ·
                refine ⟨224763034222519066164733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4794944730080406744847637 224763034222519066164733)
                ·
                  refine ⟨84286137833444649811775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224763034222519066164733 84286137833444649811775)
                  ·
                    rfl

theorem cell20_184665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_184665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184665 prefixEnd_184665 := by exact prefixLift 184665
  have htrace : WordTrace (prefixWord ++ tailWord_184665) baseStart_184665 baseEnd_184665 := by
    simpa [prefixWord, tailWord_184665, baseEnd_184665] using wordTrace_append hprefix tailTrace_184665
  have hstable : (prefixWord ++ tailWord_184665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184665).length < 2 ^ (prefixWord ++ tailWord_184665).sum := by decide
  have hdescent : baseEnd_184665 < baseStart_184665 := by decide
  rcases family_descends (prefixWord ++ tailWord_184665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184670 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_184670 : Nat := 118140960795 + 184670 * 2 ^ 59
def prefixEnd_184670 : Nat := 4983230072969 + 3 ^ 40 * 184670 * 2
def baseEnd_184670 : Nat := 84288419969686854645089

theorem tailTrace_184670 : CollatzResearch.WordTrace tailWord_184670 prefixEnd_184670 84288419969686854645089 := by
  unfold tailWord_184670
  simp only [CollatzResearch.WordTrace]
  refine ⟨841933530122450496268933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4490312160653069313434309 841933530122450496268933)
  ·
    refine ⟨157862536897959468050425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 841933530122450496268933 157862536897959468050425)
    ·
      refine ⟨118396902673469601037819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157862536897959468050425 118396902673469601037819)
      ·
        refine ⟨177595354010204401556729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118396902673469601037819 177595354010204401556729)
        ·
          refine ⟨133196515507653301167547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177595354010204401556729 133196515507653301167547)
          ·
            refine ⟨199794773261479951751321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133196515507653301167547 199794773261479951751321)
            ·
              refine ⟨149846079946109963813491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199794773261479951751321 149846079946109963813491)
              ·
                refine ⟨224769119919164945720237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149846079946109963813491 224769119919164945720237)
                ·
                  refine ⟨84288419969686854645089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224769119919164945720237 84288419969686854645089)
                  ·
                    rfl

theorem cell20_184670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_184670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184670 prefixEnd_184670 := by exact prefixLift 184670
  have htrace : WordTrace (prefixWord ++ tailWord_184670) baseStart_184670 baseEnd_184670 := by
    simpa [prefixWord, tailWord_184670, baseEnd_184670] using wordTrace_append hprefix tailTrace_184670
  have hstable : (prefixWord ++ tailWord_184670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184670).length < 2 ^ (prefixWord ++ tailWord_184670).sum := by decide
  have hdescent : baseEnd_184670 < baseStart_184670 := by decide
  rcases family_descends (prefixWord ++ tailWord_184670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184726 : List Nat := [5, 3, 1, 2, 1, 2, 1, 5]
def baseStart_184726 : Nat := 118140960795 + 184726 * 2 ^ 59
def prefixEnd_184726 : Nat := 4983230072969 + 3 ^ 40 * 184726 * 2
def baseEnd_184726 : Nat := 28104659965199849592731

theorem tailTrace_184726 : CollatzResearch.WordTrace tailWord_184726 prefixEnd_184726 28104659965199849592731 := by
  unfold tailWord_184726
  simp only [CollatzResearch.WordTrace]
  refine ⟨421094420548545345886877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4491673819184483689460021 421094420548545345886877)
  ·
    refine ⟨157910407705704504707579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 421094420548545345886877 157910407705704504707579)
    ·
      refine ⟨236865611558556757061369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157910407705704504707579 236865611558556757061369)
      ·
        refine ⟨177649208668917567796027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236865611558556757061369 177649208668917567796027)
        ·
          refine ⟨266473813003376351694041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177649208668917567796027 266473813003376351694041)
          ·
            refine ⟨199855359752532263770531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266473813003376351694041 199855359752532263770531)
            ·
              refine ⟨299783039628798395655797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199855359752532263770531 299783039628798395655797)
              ·
                refine ⟨28104659965199849592731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 299783039628798395655797 28104659965199849592731)
                ·
                  rfl

theorem cell20_184726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_184726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184726 prefixEnd_184726 := by exact prefixLift 184726
  have htrace : WordTrace (prefixWord ++ tailWord_184726) baseStart_184726 baseEnd_184726 := by
    simpa [prefixWord, tailWord_184726, baseEnd_184726] using wordTrace_append hprefix tailTrace_184726
  have hstable : (prefixWord ++ tailWord_184726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184726).length < 2 ^ (prefixWord ++ tailWord_184726).sum := by decide
  have hdescent : baseEnd_184726 < baseStart_184726 := by decide
  rcases family_descends (prefixWord ++ tailWord_184726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184741 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 3]
def baseStart_184741 : Nat := 118140960795 + 184741 * 2 ^ 59
def prefixEnd_184741 : Nat := 4983230072969 + 3 ^ 40 * 184741 * 2
def baseEnd_184741 : Nat := 84320826304326163278131

theorem tailTrace_184741 : CollatzResearch.WordTrace tailWord_184741 prefixEnd_184741 84320826304326163278131 := by
  unfold tailWord_184741
  simp only [CollatzResearch.WordTrace]
  refine ⟨6738057823722383095986077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4492038549148255397324051 6738057823722383095986077)
  ·
    refine ⟨2526771683895893660994779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6738057823722383095986077 2526771683895893660994779)
    ·
      refine ⟨3790157525843840491492169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2526771683895893660994779 3790157525843840491492169)
      ·
        refine ⟨2842618144382880368619127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3790157525843840491492169 2842618144382880368619127)
        ·
          refine ⟨4263927216574320552928691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842618144382880368619127 4263927216574320552928691)
          ·
            refine ⟨6395890824861480829393037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4263927216574320552928691 6395890824861480829393037)
            ·
              refine ⟨2398459059323055311022389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6395890824861480829393037 2398459059323055311022389)
              ·
                refine ⟨224855536811536435408349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2398459059323055311022389 224855536811536435408349)
                ·
                  refine ⟨84320826304326163278131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224855536811536435408349 84320826304326163278131)
                  ·
                    rfl

theorem cell20_184741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_184741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184741 prefixEnd_184741 := by exact prefixLift 184741
  have htrace : WordTrace (prefixWord ++ tailWord_184741) baseStart_184741 baseEnd_184741 := by
    simpa [prefixWord, tailWord_184741, baseEnd_184741] using wordTrace_append hprefix tailTrace_184741
  have hstable : (prefixWord ++ tailWord_184741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184741).length < 2 ^ (prefixWord ++ tailWord_184741).sum := by decide
  have hdescent : baseEnd_184741 < baseStart_184741 := by decide
  rcases family_descends (prefixWord ++ tailWord_184741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184744 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 4]
def baseStart_184744 : Nat := 118140960795 + 184744 * 2 ^ 59
def prefixEnd_184744 : Nat := 4983230072969 + 3 ^ 40 * 184744 * 2
def baseEnd_184744 : Nat := 84322195586071486178119

theorem tailTrace_184744 : CollatzResearch.WordTrace tailWord_184744 prefixEnd_184744 84322195586071486178119 := by
  unfold tailWord_184744
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369083621355757304172643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4492111495141009738896857 3369083621355757304172643)
  ·
    refine ⟨5053625432033635956258965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3369083621355757304172643 5053625432033635956258965)
    ·
      refine ⟨236888692126576685449639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5053625432033635956258965 236888692126576685449639)
      ·
        refine ⟨355333038189865028174459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236888692126576685449639 355333038189865028174459)
        ·
          refine ⟨532999557284797542261689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355333038189865028174459 532999557284797542261689)
          ·
            refine ⟨399749667963598156696267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532999557284797542261689 399749667963598156696267)
            ·
              refine ⟨599624501945397235044401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399749667963598156696267 599624501945397235044401)
              ·
                refine ⟨449718376459047926283301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599624501945397235044401 449718376459047926283301)
                ·
                  refine ⟨84322195586071486178119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 449718376459047926283301 84322195586071486178119)
                  ·
                    rfl

theorem cell20_184744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_184744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184744 prefixEnd_184744 := by exact prefixLift 184744
  have htrace : WordTrace (prefixWord ++ tailWord_184744) baseStart_184744 baseEnd_184744 := by
    simpa [prefixWord, tailWord_184744, baseEnd_184744] using wordTrace_append hprefix tailTrace_184744
  have hstable : (prefixWord ++ tailWord_184744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184744).length < 2 ^ (prefixWord ++ tailWord_184744).sum := by decide
  have hdescent : baseEnd_184744 < baseStart_184744 := by decide
  rcases family_descends (prefixWord ++ tailWord_184744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184793 : List Nat := [1, 2, 1, 2, 4, 1, 2, 7]
def baseStart_184793 : Nat := 118140960795 + 184793 * 2 ^ 59
def prefixEnd_184793 : Nat := 4983230072969 + 3 ^ 40 * 184793 * 2
def baseEnd_184793 : Nat := 28114853507081697848195

theorem tailTrace_184793 : CollatzResearch.WordTrace tailWord_184793 prefixEnd_184793 28114853507081697848195 := by
  unfold tailWord_184793
  simp only [CollatzResearch.WordTrace]
  refine ⟨6739954419533995976879033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4493302946355997317919355 6739954419533995976879033)
  ·
    refine ⟨5054965814650496982659275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6739954419533995976879033 5054965814650496982659275)
    ·
      refine ⟨7582448721975745473988913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5054965814650496982659275 7582448721975745473988913)
      ·
        refine ⟨5686836541481809105491685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7582448721975745473988913 5686836541481809105491685)
        ·
          refine ⟨1066281851527839207279691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5686836541481809105491685 1066281851527839207279691)
          ·
            refine ⟨1599422777291758810919537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066281851527839207279691 1599422777291758810919537)
            ·
              refine ⟨1199567082968819108189653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599422777291758810919537 1199567082968819108189653)
              ·
                refine ⟨28114853507081697848195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1199567082968819108189653 28114853507081697848195)
                ·
                  rfl

theorem cell20_184793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_184793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184793 prefixEnd_184793 := by exact prefixLift 184793
  have htrace : WordTrace (prefixWord ++ tailWord_184793) baseStart_184793 baseEnd_184793 := by
    simpa [prefixWord, tailWord_184793, baseEnd_184793] using wordTrace_append hprefix tailTrace_184793
  have hstable : (prefixWord ++ tailWord_184793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184793).length < 2 ^ (prefixWord ++ tailWord_184793).sum := by decide
  have hdescent : baseEnd_184793 < baseStart_184793 := by decide
  rcases family_descends (prefixWord ++ tailWord_184793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184802 : List Nat := [3, 3, 3, 2, 2, 1, 2, 4]
def baseStart_184802 : Nat := 118140960795 + 184802 * 2 ^ 59
def prefixEnd_184802 : Nat := 4983230072969 + 3 ^ 40 * 184802 * 2
def baseEnd_184802 : Nat := 28116222788827020748183

theorem tailTrace_184802 : CollatzResearch.WordTrace tailWord_184802 prefixEnd_184802 28116222788827020748183 := by
  unfold tailWord_184802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1685070669125347628489165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4493521784334260342637773 1685070669125347628489165)
  ·
    refine ⟨631901500922005360683437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1685070669125347628489165 631901500922005360683437)
    ·
      refine ⟨236963062845752010256289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 631901500922005360683437 236963062845752010256289)
      ·
        refine ⟨177722297134314007692217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236963062845752010256289 177722297134314007692217)
        ·
          refine ⟨133291722850735505769163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177722297134314007692217 133291722850735505769163)
          ·
            refine ⟨199937584276103258653745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133291722850735505769163 199937584276103258653745)
            ·
              refine ⟨149953188207077443990309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199937584276103258653745 149953188207077443990309)
              ·
                refine ⟨28116222788827020748183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149953188207077443990309 28116222788827020748183)
                ·
                  rfl

theorem cell20_184802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_184802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184802 prefixEnd_184802 := by exact prefixLift 184802
  have htrace : WordTrace (prefixWord ++ tailWord_184802) baseStart_184802 baseEnd_184802 := by
    simpa [prefixWord, tailWord_184802, baseEnd_184802] using wordTrace_append hprefix tailTrace_184802
  have hstable : (prefixWord ++ tailWord_184802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184802).length < 2 ^ (prefixWord ++ tailWord_184802).sum := by decide
  have hdescent : baseEnd_184802 < baseStart_184802 := by decide
  rcases family_descends (prefixWord ++ tailWord_184802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184810 : List Nat := [3, 1, 3, 1, 3, 2, 1, 6]
def baseStart_184810 : Nat := 118140960795 + 184810 * 2 ^ 59
def prefixEnd_184810 : Nat := 4983230072969 + 3 ^ 40 * 184810 * 2
def baseEnd_184810 : Nat := 28117439928156196659283

theorem tailTrace_184810 : CollatzResearch.WordTrace tailWord_184810 prefixEnd_184810 28117439928156196659283 := by
  unfold tailWord_184810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1685143615118101970061971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4493716306981605253498589 1685143615118101970061971)
  ·
    refine ⟨2527715422677152955092957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1685143615118101970061971 2527715422677152955092957)
    ·
      refine ⟨947893283503932358159859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2527715422677152955092957 947893283503932358159859)
      ·
        refine ⟨1421839925255898537239789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947893283503932358159859 1421839925255898537239789)
        ·
          refine ⟨533189971970961951464921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1421839925255898537239789 533189971970961951464921)
          ·
            refine ⟨399892478978221463598691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533189971970961951464921 399892478978221463598691)
            ·
              refine ⟨599838718467332195398037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399892478978221463598691 599838718467332195398037)
              ·
                refine ⟨28117439928156196659283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 599838718467332195398037 28117439928156196659283)
                ·
                  rfl

theorem cell20_184810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_184810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184810 prefixEnd_184810 := by exact prefixLift 184810
  have htrace : WordTrace (prefixWord ++ tailWord_184810) baseStart_184810 baseEnd_184810 := by
    simpa [prefixWord, tailWord_184810, baseEnd_184810] using wordTrace_append hprefix tailTrace_184810
  have hstable : (prefixWord ++ tailWord_184810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184810).length < 2 ^ (prefixWord ++ tailWord_184810).sum := by decide
  have hdescent : baseEnd_184810 < baseStart_184810 := by decide
  rcases family_descends (prefixWord ++ tailWord_184810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184869 : List Nat := [1, 3, 1, 2, 2, 1, 4, 6]
def baseStart_184869 : Nat := 118140960795 + 184869 * 2 ^ 59
def prefixEnd_184869 : Nat := 4983230072969 + 3 ^ 40 * 184869 * 2
def baseEnd_184869 : Nat := 28126416330708869003647

theorem tailTrace_184869 : CollatzResearch.WordTrace tailWord_184869 prefixEnd_184869 28126416330708869003647 := by
  unfold tailWord_184869
  simp only [CollatzResearch.WordTrace]
  refine ⟨6742726367258660956645661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4495150911505773971097107 6742726367258660956645661)
  ·
    refine ⟨2528522387721997858742123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6742726367258660956645661 2528522387721997858742123)
    ·
      refine ⟨3792783581582996788113185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2528522387721997858742123 3792783581582996788113185)
      ·
        refine ⟨2844587686187247591084889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3792783581582996788113185 2844587686187247591084889)
        ·
          refine ⟨2133440764640435693313667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2844587686187247591084889 2133440764640435693313667)
          ·
            refine ⟨3200161146960653539970501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133440764640435693313667 3200161146960653539970501)
            ·
              refine ⟨600030215055122538744469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3200161146960653539970501 600030215055122538744469)
              ·
                refine ⟨28126416330708869003647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 600030215055122538744469 28126416330708869003647)
                ·
                  rfl

theorem cell20_184869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_184869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184869 prefixEnd_184869 := by exact prefixLift 184869
  have htrace : WordTrace (prefixWord ++ tailWord_184869) baseStart_184869 baseEnd_184869 := by
    simpa [prefixWord, tailWord_184869, baseEnd_184869] using wordTrace_append hprefix tailTrace_184869
  have hstable : (prefixWord ++ tailWord_184869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184869).length < 2 ^ (prefixWord ++ tailWord_184869).sum := by decide
  have hdescent : baseEnd_184869 < baseStart_184869 := by decide
  rcases family_descends (prefixWord ++ tailWord_184869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184876 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_184876 : Nat := 118140960795 + 184876 * 2 ^ 59
def prefixEnd_184876 : Nat := 4983230072969 + 3 ^ 40 * 184876 * 2
def baseEnd_184876 : Nat := 84382443982865693777579

theorem tailTrace_184876 : CollatzResearch.WordTrace tailWord_184876 prefixEnd_184876 84382443982865693777579 := by
  unfold tailWord_184876
  simp only [CollatzResearch.WordTrace]
  refine ⟨3371490839116650576075241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4495321118822200768100321 3371490839116650576075241)
  ·
    refine ⟨2528618129337487932056431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3371490839116650576075241 2528618129337487932056431)
    ·
      refine ⟨3792927194006231898084647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2528618129337487932056431 3792927194006231898084647)
      ·
        refine ⟨5689390791009347847126971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3792927194006231898084647 5689390791009347847126971)
        ·
          refine ⟨8534086186514021770690457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5689390791009347847126971 8534086186514021770690457)
          ·
            refine ⟨6400564639885516328017843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8534086186514021770690457 6400564639885516328017843)
            ·
              refine ⟨9600846959828274492026765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6400564639885516328017843 9600846959828274492026765)
              ·
                refine ⟨3600317609935602934510037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9600846959828274492026765 3600317609935602934510037)
                ·
                  refine ⟨84382443982865693777579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3600317609935602934510037 84382443982865693777579)
                  ·
                    rfl

theorem cell20_184876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_184876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184876 prefixEnd_184876 := by exact prefixLift 184876
  have htrace : WordTrace (prefixWord ++ tailWord_184876) baseStart_184876 baseEnd_184876 := by
    simpa [prefixWord, tailWord_184876, baseEnd_184876] using wordTrace_append hprefix tailTrace_184876
  have hstable : (prefixWord ++ tailWord_184876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184876).length < 2 ^ (prefixWord ++ tailWord_184876).sum := by decide
  have hdescent : baseEnd_184876 < baseStart_184876 := by decide
  rcases family_descends (prefixWord ++ tailWord_184876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184886 : List Nat := [5, 1, 2, 1, 2, 9]
def baseStart_184886 : Nat := 118140960795 + 184886 * 2 ^ 59
def prefixEnd_184886 : Nat := 4983230072969 + 3 ^ 40 * 184886 * 2
def baseEnd_184886 : Nat := 3125444750198151979415

theorem tailTrace_184886 : CollatzResearch.WordTrace tailWord_184886 prefixEnd_184886 3125444750198151979415 := by
  unfold tailWord_184886
  simp only [CollatzResearch.WordTrace]
  refine ⟨421459150512317053750907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4495564272131381906676341 421459150512317053750907)
  ·
    refine ⟨632188725768475580626361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 421459150512317053750907 632188725768475580626361)
    ·
      refine ⟨474141544326356685469771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 632188725768475580626361 474141544326356685469771)
      ·
        refine ⟨711212316489535028204657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474141544326356685469771 711212316489535028204657)
        ·
          refine ⟨533409237367151271153493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 711212316489535028204657 533409237367151271153493)
          ·
            refine ⟨3125444750198151979415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 533409237367151271153493 3125444750198151979415)
            ·
              rfl

theorem cell20_184886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 9].length) (baseStart_184886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184886 prefixEnd_184886 := by exact prefixLift 184886
  have htrace : WordTrace (prefixWord ++ tailWord_184886) baseStart_184886 baseEnd_184886 := by
    simpa [prefixWord, tailWord_184886, baseEnd_184886] using wordTrace_append hprefix tailTrace_184886
  have hstable : (prefixWord ++ tailWord_184886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184886).length < 2 ^ (prefixWord ++ tailWord_184886).sum := by decide
  have hdescent : baseEnd_184886 < baseStart_184886 := by decide
  rcases family_descends (prefixWord ++ tailWord_184886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184896 : List Nat := [2, 1, 1, 2, 2, 2, 6, 2, 2]
def baseStart_184896 : Nat := 118140960795 + 184896 * 2 ^ 59
def prefixEnd_184896 : Nat := 4983230072969 + 3 ^ 40 * 184896 * 2
def baseEnd_184896 : Nat := 84391572527834513110831

theorem tailTrace_184896 : CollatzResearch.WordTrace tailWord_184896 prefixEnd_184896 84391572527834513110831 := by
  unfold tailWord_184896
  simp only [CollatzResearch.WordTrace]
  refine ⟨3371855569080422283939271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4495807425440563045252361 3371855569080422283939271)
  ·
    refine ⟨5057783353620633425908907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3371855569080422283939271 5057783353620633425908907)
    ·
      refine ⟨7586675030430950138863361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5057783353620633425908907 7586675030430950138863361)
      ·
        refine ⟨5690006272823212604147521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7586675030430950138863361 5690006272823212604147521)
        ·
          refine ⟨4267504704617409453110641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5690006272823212604147521 4267504704617409453110641)
          ·
            refine ⟨3200628528463057089832981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4267504704617409453110641 3200628528463057089832981)
            ·
              refine ⟨150029462271705801085921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3200628528463057089832981 150029462271705801085921)
              ·
                refine ⟨112522096703779350814441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150029462271705801085921 112522096703779350814441)
                ·
                  refine ⟨84391572527834513110831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112522096703779350814441 84391572527834513110831)
                  ·
                    rfl

theorem cell20_184896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 2].length) (baseStart_184896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184896 prefixEnd_184896 := by exact prefixLift 184896
  have htrace : WordTrace (prefixWord ++ tailWord_184896) baseStart_184896 baseEnd_184896 := by
    simpa [prefixWord, tailWord_184896, baseEnd_184896] using wordTrace_append hprefix tailTrace_184896
  have hstable : (prefixWord ++ tailWord_184896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184896).length < 2 ^ (prefixWord ++ tailWord_184896).sum := by decide
  have hdescent : baseEnd_184896 < baseStart_184896 := by decide
  rcases family_descends (prefixWord ++ tailWord_184896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184907 : List Nat := [1, 1, 1, 1, 3, 1, 7, 5]
def baseStart_184907 : Nat := 118140960795 + 184907 * 2 ^ 59
def prefixEnd_184907 : Nat := 4983230072969 + 3 ^ 40 * 184907 * 2
def baseEnd_184907 : Nat := 28132197742522454581373

theorem tailTrace_184907 : CollatzResearch.WordTrace tailWord_184907 prefixEnd_184907 28132197742522454581373 := by
  unfold tailWord_184907
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744112341120993446528975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4496074894080662297685983 6744112341120993446528975)
  ·
    refine ⟨10116168511681490169793463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6744112341120993446528975 10116168511681490169793463)
    ·
      refine ⟨15174252767522235254690195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10116168511681490169793463 15174252767522235254690195)
      ·
        refine ⟨22761379151283352882035293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15174252767522235254690195 22761379151283352882035293)
        ·
          refine ⟨8535517181731257330763235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22761379151283352882035293 8535517181731257330763235)
          ·
            refine ⟨12803275772596885996144853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8535517181731257330763235 12803275772596885996144853)
            ·
              refine ⟨300076775920239515534645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12803275772596885996144853 300076775920239515534645)
              ·
                refine ⟨28132197742522454581373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 300076775920239515534645 28132197742522454581373)
                ·
                  rfl

theorem cell20_184907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_184907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184907 prefixEnd_184907 := by exact prefixLift 184907
  have htrace : WordTrace (prefixWord ++ tailWord_184907) baseStart_184907 baseEnd_184907 := by
    simpa [prefixWord, tailWord_184907, baseEnd_184907] using wordTrace_append hprefix tailTrace_184907
  have hstable : (prefixWord ++ tailWord_184907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184907).length < 2 ^ (prefixWord ++ tailWord_184907).sum := by decide
  have hdescent : baseEnd_184907 < baseStart_184907 := by decide
  rcases family_descends (prefixWord ++ tailWord_184907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184930 : List Nat := [3, 3, 2, 3, 1, 1, 2, 3, 2]
def baseStart_184930 : Nat := 118140960795 + 184930 * 2 ^ 59
def prefixEnd_184930 : Nat := 4983230072969 + 3 ^ 40 * 184930 * 2
def baseEnd_184930 : Nat := 84407091054281505977359

theorem tailTrace_184930 : CollatzResearch.WordTrace tailWord_184930 prefixEnd_184930 84407091054281505977359 := by
  unfold tailWord_184930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686237805009417093654061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4496634146691778916410829 1686237805009417093654061)
  ·
    refine ⟨632339176878531410120273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1686237805009417093654061 632339176878531410120273)
    ·
      refine ⟨474254382658898557590205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 632339176878531410120273 474254382658898557590205)
      ·
        refine ⟨177845393497086959096327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474254382658898557590205 177845393497086959096327)
        ·
          refine ⟨266768090245630438644491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177845393497086959096327 266768090245630438644491)
          ·
            refine ⟨400152135368445657966737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266768090245630438644491 400152135368445657966737)
            ·
              refine ⟨300114101526334243475053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400152135368445657966737 300114101526334243475053)
              ·
                refine ⟨112542788072375341303145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300114101526334243475053 112542788072375341303145)
                ·
                  refine ⟨84407091054281505977359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112542788072375341303145 84407091054281505977359)
                  ·
                    rfl

theorem cell20_184930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_184930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184930 prefixEnd_184930 := by exact prefixLift 184930
  have htrace : WordTrace (prefixWord ++ tailWord_184930) baseStart_184930 baseEnd_184930 := by
    simpa [prefixWord, tailWord_184930, baseEnd_184930] using wordTrace_append hprefix tailTrace_184930
  have hstable : (prefixWord ++ tailWord_184930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184930).length < 2 ^ (prefixWord ++ tailWord_184930).sum := by decide
  have hdescent : baseEnd_184930 < baseStart_184930 := by decide
  rcases family_descends (prefixWord ++ tailWord_184930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184938 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_184938 : Nat := 118140960795 + 184938 * 2 ^ 59
def prefixEnd_184938 : Nat := 4983230072969 + 3 ^ 40 * 184938 * 2
def baseEnd_184938 : Nat := 84410742472269033710659

theorem tailTrace_184938 : CollatzResearch.WordTrace tailWord_184938 prefixEnd_184938 84410742472269033710659 := by
  unfold tailWord_184938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686310751002171435226867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4496828669339123827271645 1686310751002171435226867)
  ·
    refine ⟨2529466126503257152840301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1686310751002171435226867 2529466126503257152840301)
    ·
      refine ⟨948549797438721432315113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2529466126503257152840301 948549797438721432315113)
      ·
        refine ⟨711412348079041074236335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 948549797438721432315113 711412348079041074236335)
        ·
          refine ⟨1067118522118561611354503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711412348079041074236335 1067118522118561611354503)
          ·
            refine ⟨1600677783177842417031755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067118522118561611354503 1600677783177842417031755)
            ·
              refine ⟨2401016674766763625547633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600677783177842417031755 2401016674766763625547633)
              ·
                refine ⟨1800762506075072719160725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2401016674766763625547633 1800762506075072719160725)
                ·
                  refine ⟨84410742472269033710659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1800762506075072719160725 84410742472269033710659)
                  ·
                    rfl

theorem cell20_184938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_184938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184938 prefixEnd_184938 := by exact prefixLift 184938
  have htrace : WordTrace (prefixWord ++ tailWord_184938) baseStart_184938 baseEnd_184938 := by
    simpa [prefixWord, tailWord_184938, baseEnd_184938] using wordTrace_append hprefix tailTrace_184938
  have hstable : (prefixWord ++ tailWord_184938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184938).length < 2 ^ (prefixWord ++ tailWord_184938).sum := by decide
  have hdescent : baseEnd_184938 < baseStart_184938 := by decide
  rcases family_descends (prefixWord ++ tailWord_184938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184952 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_184952 : Nat := 118140960795 + 184952 * 2 ^ 59
def prefixEnd_184952 : Nat := 4983230072969 + 3 ^ 40 * 184952 * 2
def baseEnd_184952 : Nat := 84417132453747207243935

theorem tailTrace_184952 : CollatzResearch.WordTrace tailWord_184952 prefixEnd_184952 84417132453747207243935 := by
  unfold tailWord_184952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3372876812978983065958555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4497169083971977421278073 3372876812978983065958555)
  ·
    refine ⟨5059315219468474598937833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3372876812978983065958555 5059315219468474598937833)
    ·
      refine ⟨3794486414601355949203375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5059315219468474598937833 3794486414601355949203375)
      ·
        refine ⟨5691729621902033923805063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3794486414601355949203375 5691729621902033923805063)
        ·
          refine ⟨8537594432853050885707595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5691729621902033923805063 8537594432853050885707595)
          ·
            refine ⟨12806391649279576328561393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8537594432853050885707595 12806391649279576328561393)
            ·
              refine ⟨9604793736959682246421045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12806391649279576328561393 9604793736959682246421045)
              ·
                refine ⟨900449412839970210601973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9604793736959682246421045 900449412839970210601973)
                ·
                  refine ⟨84417132453747207243935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 900449412839970210601973 84417132453747207243935)
                  ·
                    rfl

theorem cell20_184952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_184952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184952 prefixEnd_184952 := by exact prefixLift 184952
  have htrace : WordTrace (prefixWord ++ tailWord_184952) baseStart_184952 baseEnd_184952 := by
    simpa [prefixWord, tailWord_184952, baseEnd_184952] using wordTrace_append hprefix tailTrace_184952
  have hstable : (prefixWord ++ tailWord_184952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184952).length < 2 ^ (prefixWord ++ tailWord_184952).sum := by decide
  have hdescent : baseEnd_184952 < baseStart_184952 := by decide
  rcases family_descends (prefixWord ++ tailWord_184952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184983 : List Nat := [1, 1, 3, 3, 2, 1, 3, 6]
def baseStart_184983 : Nat := 118140960795 + 184983 * 2 ^ 59
def prefixEnd_184983 : Nat := 4983230072969 + 3 ^ 40 * 184983 * 2
def baseEnd_184983 : Nat := 28143760566149625736825

theorem tailTrace_184983 : CollatzResearch.WordTrace tailWord_184983 prefixEnd_184983 28143760566149625736825 := by
  unfold tailWord_184983
  simp only [CollatzResearch.WordTrace]
  refine ⟨6746884288845658426295603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4497922859230438950863735 6746884288845658426295603)
  ·
    refine ⟨10120326433268487639443405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6746884288845658426295603 10120326433268487639443405)
    ·
      refine ⟨3795122412475682864791277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10120326433268487639443405 3795122412475682864791277)
      ·
        refine ⟨1423170904678381074296729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3795122412475682864791277 1423170904678381074296729)
        ·
          refine ⟨1067378178508785805722547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1423170904678381074296729 1067378178508785805722547)
          ·
            refine ⟨1601067267763178708583821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067378178508785805722547 1601067267763178708583821)
            ·
              refine ⟨600400225411192015718933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1601067267763178708583821 600400225411192015718933)
              ·
                refine ⟨28143760566149625736825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 600400225411192015718933 28143760566149625736825)
                ·
                  rfl

theorem cell20_184983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_184983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_184983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_184983 prefixEnd_184983 := by exact prefixLift 184983
  have htrace : WordTrace (prefixWord ++ tailWord_184983) baseStart_184983 baseEnd_184983 := by
    simpa [prefixWord, tailWord_184983, baseEnd_184983] using wordTrace_append hprefix tailTrace_184983
  have hstable : (prefixWord ++ tailWord_184983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184983).length < 2 ^ (prefixWord ++ tailWord_184983).sum := by decide
  have hdescent : baseEnd_184983 < baseStart_184983 := by decide
  rcases family_descends (prefixWord ++ tailWord_184983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185006 : List Nat := [4, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_185006 : Nat := 118140960795 + 185006 * 2 ^ 59
def prefixEnd_185006 : Nat := 4983230072969 + 3 ^ 40 * 185006 * 2
def baseEnd_185006 : Nat := 84441779525163019443715

theorem tailTrace_185006 : CollatzResearch.WordTrace tailWord_185006 prefixEnd_185006 84441779525163019443715 := by
  unfold tailWord_185006
  simp only [CollatzResearch.WordTrace]
  refine ⟨843465395970291669297859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4498482111841555569588581 843465395970291669297859)
  ·
    refine ⟨1265198093955437503946789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 843465395970291669297859 1265198093955437503946789)
    ·
      refine ⟨237224642616644531990023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1265198093955437503946789 237224642616644531990023)
      ·
        refine ⟨355836963924966797985035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237224642616644531990023 355836963924966797985035)
        ·
          refine ⟨533755445887450196977553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355836963924966797985035 533755445887450196977553)
          ·
            refine ⟨400316584415587647733165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533755445887450196977553 400316584415587647733165)
            ·
              refine ⟨150118719155845367899937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 400316584415587647733165 150118719155845367899937)
              ·
                refine ⟨112589039366884025924953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150118719155845367899937 112589039366884025924953)
                ·
                  refine ⟨84441779525163019443715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112589039366884025924953 84441779525163019443715)
                  ·
                    rfl

theorem cell20_185006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_185006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185006 prefixEnd_185006 := by exact prefixLift 185006
  have htrace : WordTrace (prefixWord ++ tailWord_185006) baseStart_185006 baseEnd_185006 := by
    simpa [prefixWord, tailWord_185006, baseEnd_185006] using wordTrace_append hprefix tailTrace_185006
  have hstable : (prefixWord ++ tailWord_185006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185006).length < 2 ^ (prefixWord ++ tailWord_185006).sum := by decide
  have hdescent : baseEnd_185006 < baseStart_185006 := by decide
  rcases family_descends (prefixWord ++ tailWord_185006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185021 : List Nat := [1, 4, 1, 2, 1, 3, 1, 7]
def baseStart_185021 : Nat := 118140960795 + 185021 * 2 ^ 59
def prefixEnd_185021 : Nat := 4983230072969 + 3 ^ 40 * 185021 * 2
def baseEnd_185021 : Nat := 28149541977963211314551

theorem tailTrace_185021 : CollatzResearch.WordTrace tailWord_185021 prefixEnd_185021 28149541977963211314551 := by
  unfold tailWord_185021
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748270262707990916178917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4498846841805327277452611 6748270262707990916178917)
  ·
    refine ⟨1265300674257748296783547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6748270262707990916178917 1265300674257748296783547)
    ·
      refine ⟨1897951011386622445175321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1265300674257748296783547 1897951011386622445175321)
      ·
        refine ⟨1423463258539966833881491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1897951011386622445175321 1423463258539966833881491)
        ·
          refine ⟨2135194887809950250822237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423463258539966833881491 2135194887809950250822237)
          ·
            refine ⟨800698082928731344058339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2135194887809950250822237 800698082928731344058339)
            ·
              refine ⟨1201047124393097016087509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800698082928731344058339 1201047124393097016087509)
              ·
                refine ⟨28149541977963211314551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1201047124393097016087509 28149541977963211314551)
                ·
                  rfl

theorem cell20_185021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_185021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185021 prefixEnd_185021 := by exact prefixLift 185021
  have htrace : WordTrace (prefixWord ++ tailWord_185021) baseStart_185021 baseEnd_185021 := by
    simpa [prefixWord, tailWord_185021, baseEnd_185021] using wordTrace_append hprefix tailTrace_185021
  have hstable : (prefixWord ++ tailWord_185021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185021).length < 2 ^ (prefixWord ++ tailWord_185021).sum := by decide
  have hdescent : baseEnd_185021 < baseStart_185021 := by decide
  rcases family_descends (prefixWord ++ tailWord_185021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185024 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 3]
def baseStart_185024 : Nat := 118140960795 + 185024 * 2 ^ 59
def prefixEnd_185024 : Nat := 4983230072969 + 3 ^ 40 * 185024 * 2
def baseEnd_185024 : Nat := 84449995215634956843641

theorem tailTrace_185024 : CollatzResearch.WordTrace tailWord_185024 prefixEnd_185024 84449995215634956843641 := by
  unfold tailWord_185024
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374189840848561214269063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4498919787798081619025417 3374189840848561214269063)
  ·
    refine ⟨5061284761272841821403595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3374189840848561214269063 5061284761272841821403595)
    ·
      refine ⟨7591927141909262732105393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5061284761272841821403595 7591927141909262732105393)
      ·
        refine ⟨5693945356431947049079045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7591927141909262732105393 5693945356431947049079045)
        ·
          refine ⟨1067614754330990071702321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5693945356431947049079045 1067614754330990071702321)
          ·
            refine ⟨800711065748242553776741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1067614754330990071702321 800711065748242553776741)
            ·
              refine ⟨150133324827795478833139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 800711065748242553776741 150133324827795478833139)
              ·
                refine ⟨225199987241693218249709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150133324827795478833139 225199987241693218249709)
                ·
                  refine ⟨84449995215634956843641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225199987241693218249709 84449995215634956843641)
                  ·
                    rfl

theorem cell20_185024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_185024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185024 prefixEnd_185024 := by exact prefixLift 185024
  have htrace : WordTrace (prefixWord ++ tailWord_185024) baseStart_185024 baseEnd_185024 := by
    simpa [prefixWord, tailWord_185024, baseEnd_185024] using wordTrace_append hprefix tailTrace_185024
  have hstable : (prefixWord ++ tailWord_185024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185024).length < 2 ^ (prefixWord ++ tailWord_185024).sum := by decide
  have hdescent : baseEnd_185024 < baseStart_185024 := by decide
  rcases family_descends (prefixWord ++ tailWord_185024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185059 : List Nat := [1, 1, 1, 7, 1, 9]
def baseStart_185059 : Nat := 118140960795 + 185059 * 2 ^ 59
def prefixEnd_185059 : Nat := 4983230072969 + 3 ^ 40 * 185059 * 2
def baseEnd_185059 : Nat := 3128369265530755210253

theorem tailTrace_185059 : CollatzResearch.WordTrace tailWord_185059 prefixEnd_185059 3128369265530755210253 := by
  unfold tailWord_185059
  simp only [CollatzResearch.WordTrace]
  refine ⟨6749656236570323406062231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4499770824380215604041487 6749656236570323406062231)
  ·
    refine ⟨10124484354855485109093347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6749656236570323406062231 10124484354855485109093347)
    ·
      refine ⟨15186726532283227663640021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10124484354855485109093347 15186726532283227663640021)
      ·
        refine ⟨355938903100388148366563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 15186726532283227663640021 355938903100388148366563)
        ·
          refine ⟨533908354650582222549845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355938903100388148366563 533908354650582222549845)
          ·
            refine ⟨3128369265530755210253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 533908354650582222549845 3128369265530755210253)
            ·
              rfl

theorem cell20_185059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 9].length) (baseStart_185059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185059 prefixEnd_185059 := by exact prefixLift 185059
  have htrace : WordTrace (prefixWord ++ tailWord_185059) baseStart_185059 baseEnd_185059 := by
    simpa [prefixWord, tailWord_185059, baseEnd_185059] using wordTrace_append hprefix tailTrace_185059
  have hstable : (prefixWord ++ tailWord_185059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185059).length < 2 ^ (prefixWord ++ tailWord_185059).sum := by decide
  have hdescent : baseEnd_185059 < baseStart_185059 := by decide
  rcases family_descends (prefixWord ++ tailWord_185059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185107 : List Nat := [1, 1, 1, 2, 1, 3, 6, 3, 2]
def baseStart_185107 : Nat := 118140960795 + 185107 * 2 ^ 59
def prefixEnd_185107 : Nat := 4983230072969 + 3 ^ 40 * 185107 * 2
def baseEnd_185107 : Nat := 84487878677255557076635

theorem tailTrace_185107 : CollatzResearch.WordTrace tailWord_185107 prefixEnd_185107 84487878677255557076635 := by
  unfold tailWord_185107
  simp only [CollatzResearch.WordTrace]
  refine ⟨6751406940396427603809575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4500937960264285069206383 6751406940396427603809575)
  ·
    refine ⟨10127110410594641405714363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6751406940396427603809575 10127110410594641405714363)
    ·
      refine ⟨15190665615891962108571545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10127110410594641405714363 15190665615891962108571545)
      ·
        refine ⟨11392999211918971581428659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15190665615891962108571545 11392999211918971581428659)
        ·
          refine ⟨17089498817878457372142989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11392999211918971581428659 17089498817878457372142989)
          ·
            refine ⟨6408562056704421514553621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17089498817878457372142989 6408562056704421514553621)
            ·
              refine ⟨300401346408019758494701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6408562056704421514553621 300401346408019758494701)
              ·
                refine ⟨112650504903007409435513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300401346408019758494701 112650504903007409435513)
                ·
                  refine ⟨84487878677255557076635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112650504903007409435513 84487878677255557076635)
                  ·
                    rfl

theorem cell20_185107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 2].length) (baseStart_185107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185107 prefixEnd_185107 := by exact prefixLift 185107
  have htrace : WordTrace (prefixWord ++ tailWord_185107) baseStart_185107 baseEnd_185107 := by
    simpa [prefixWord, tailWord_185107, baseEnd_185107] using wordTrace_append hprefix tailTrace_185107
  have hstable : (prefixWord ++ tailWord_185107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185107).length < 2 ^ (prefixWord ++ tailWord_185107).sum := by decide
  have hdescent : baseEnd_185107 < baseStart_185107 := by decide
  rcases family_descends (prefixWord ++ tailWord_185107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185138 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_185138 : Nat := 118140960795 + 185138 * 2 ^ 59
def prefixEnd_185138 : Nat := 4983230072969 + 3 ^ 40 * 185138 * 2
def baseEnd_185138 : Nat := 84502027921957227043175

theorem tailTrace_185138 : CollatzResearch.WordTrace tailWord_185138 prefixEnd_185138 84502027921957227043175 := by
  unfold tailWord_185138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1688134400821029974547017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4501691735522746598792045 1688134400821029974547017)
  ·
    refine ⟨1266100800615772480910263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1688134400821029974547017 1266100800615772480910263)
    ·
      refine ⟨1899151200923658721365395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1266100800615772480910263 1899151200923658721365395)
      ·
        refine ⟨2848726801385488082048093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899151200923658721365395 2848726801385488082048093)
        ·
          refine ⟨1068272550519558030768035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2848726801385488082048093 1068272550519558030768035)
          ·
            refine ⟨1602408825779337046152053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068272550519558030768035 1602408825779337046152053)
            ·
              refine ⟨150225827416812848076755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1602408825779337046152053 150225827416812848076755)
              ·
                refine ⟨225338741125219272115133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150225827416812848076755 225338741125219272115133)
                ·
                  refine ⟨84502027921957227043175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225338741125219272115133 84502027921957227043175)
                  ·
                    rfl

theorem cell20_185138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_185138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185138 prefixEnd_185138 := by exact prefixLift 185138
  have htrace : WordTrace (prefixWord ++ tailWord_185138) baseStart_185138 baseEnd_185138 := by
    simpa [prefixWord, tailWord_185138, baseEnd_185138] using wordTrace_append hprefix tailTrace_185138
  have hstable : (prefixWord ++ tailWord_185138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185138).length < 2 ^ (prefixWord ++ tailWord_185138).sum := by decide
  have hdescent : baseEnd_185138 < baseStart_185138 := by decide
  rcases family_descends (prefixWord ++ tailWord_185138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185234 : List Nat := [3, 2, 3, 2, 2, 2, 2, 2, 2]
def baseStart_185234 : Nat := 118140960795 + 185234 * 2 ^ 59
def prefixEnd_185234 : Nat := 4983230072969 + 3 ^ 40 * 185234 * 2
def baseEnd_185234 : Nat := 84545844937807559842783

theorem tailTrace_185234 : CollatzResearch.WordTrace tailWord_185234 prefixEnd_185234 84545844937807559842783 := by
  unfold tailWord_185234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689009752734082073420689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4504026007290885529121837 1689009752734082073420689)
  ·
    refine ⟨1266757314550561555065517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1689009752734082073420689 1266757314550561555065517)
    ·
      refine ⟨475033992956460583149569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1266757314550561555065517 475033992956460583149569)
      ·
        refine ⟨356275494717345437362177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475033992956460583149569 356275494717345437362177)
        ·
          refine ⟨267206621038009078021633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356275494717345437362177 267206621038009078021633)
          ·
            refine ⟨200404965778506808516225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267206621038009078021633 200404965778506808516225)
            ·
              refine ⟨150303724333880106387169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200404965778506808516225 150303724333880106387169)
              ·
                refine ⟨112727793250410079790377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150303724333880106387169 112727793250410079790377)
                ·
                  refine ⟨84545844937807559842783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112727793250410079790377 84545844937807559842783)
                  ·
                    rfl

theorem cell20_185234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_185234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185234 prefixEnd_185234 := by exact prefixLift 185234
  have htrace : WordTrace (prefixWord ++ tailWord_185234) baseStart_185234 baseEnd_185234 := by
    simpa [prefixWord, tailWord_185234, baseEnd_185234] using wordTrace_append hprefix tailTrace_185234
  have hstable : (prefixWord ++ tailWord_185234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185234).length < 2 ^ (prefixWord ++ tailWord_185234).sum := by decide
  have hdescent : baseEnd_185234 < baseStart_185234 := by decide
  rcases family_descends (prefixWord ++ tailWord_185234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185352 : List Nat := [2, 1, 3, 2, 1, 4, 3, 2, 2]
def baseStart_185352 : Nat := 118140960795 + 185352 * 2 ^ 59
def prefixEnd_185352 : Nat := 4983230072969 + 3 ^ 40 * 185352 * 2
def baseEnd_185352 : Nat := 84599703353123593908967

theorem tailTrace_185352 : CollatzResearch.WordTrace tailWord_185352 prefixEnd_185352 84599703353123593908967 := by
  unfold tailWord_185352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3380171412254417223239155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4506895216339222964318873 3380171412254417223239155)
  ·
    refine ⟨5070257118381625834858733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3380171412254417223239155 5070257118381625834858733)
    ·
      refine ⟨1901346419393109688072025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5070257118381625834858733 1901346419393109688072025)
      ·
        refine ⟨1426009814544832266054019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1901346419393109688072025 1426009814544832266054019)
        ·
          refine ⟨2139014721817248399081029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426009814544832266054019 2139014721817248399081029)
          ·
            refine ⟨401065260340734074827693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2139014721817248399081029 401065260340734074827693)
            ·
              refine ⟨150399472627775278060385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401065260340734074827693 150399472627775278060385)
              ·
                refine ⟨112799604470831458545289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150399472627775278060385 112799604470831458545289)
                ·
                  refine ⟨84599703353123593908967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112799604470831458545289 84599703353123593908967)
                  ·
                    rfl

theorem cell20_185352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 2].length) (baseStart_185352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185352 prefixEnd_185352 := by exact prefixLift 185352
  have htrace : WordTrace (prefixWord ++ tailWord_185352) baseStart_185352 baseEnd_185352 := by
    simpa [prefixWord, tailWord_185352, baseEnd_185352] using wordTrace_append hprefix tailTrace_185352
  have hstable : (prefixWord ++ tailWord_185352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185352).length < 2 ^ (prefixWord ++ tailWord_185352).sum := by decide
  have hdescent : baseEnd_185352 < baseStart_185352 := by decide
  rcases family_descends (prefixWord ++ tailWord_185352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185356 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_185356 : Nat := 118140960795 + 185356 * 2 ^ 59
def prefixEnd_185356 : Nat := 4983230072969 + 3 ^ 40 * 185356 * 2
def baseEnd_185356 : Nat := 84601529062117357775617

theorem tailTrace_185356 : CollatzResearch.WordTrace tailWord_185356 prefixEnd_185356 84601529062117357775617 := by
  unfold tailWord_185356
  simp only [CollatzResearch.WordTrace]
  refine ⟨3380244358247171564811961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4506992477662895419749281 3380244358247171564811961)
  ·
    refine ⟨2535183268685378673608971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3380244358247171564811961 2535183268685378673608971)
    ·
      refine ⟨3802774903028068010413457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2535183268685378673608971 3802774903028068010413457)
      ·
        refine ⟨2852081177271051007810093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3802774903028068010413457 2852081177271051007810093)
        ·
          refine ⟨1069530441476644127928785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2852081177271051007810093 1069530441476644127928785)
          ·
            refine ⟨802147831107483095946589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1069530441476644127928785 802147831107483095946589)
            ·
              refine ⟨300805436665306160979971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 802147831107483095946589 300805436665306160979971)
              ·
                refine ⟨451208154997959241469957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300805436665306160979971 451208154997959241469957)
                ·
                  refine ⟨84601529062117357775617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 451208154997959241469957 84601529062117357775617)
                  ·
                    rfl

theorem cell20_185356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_185356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185356 prefixEnd_185356 := by exact prefixLift 185356
  have htrace : WordTrace (prefixWord ++ tailWord_185356) baseStart_185356 baseEnd_185356 := by
    simpa [prefixWord, tailWord_185356, baseEnd_185356] using wordTrace_append hprefix tailTrace_185356
  have hstable : (prefixWord ++ tailWord_185356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185356).length < 2 ^ (prefixWord ++ tailWord_185356).sum := by decide
  have hdescent : baseEnd_185356 < baseStart_185356 := by decide
  rcases family_descends (prefixWord ++ tailWord_185356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185362 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 3]
def baseStart_185362 : Nat := 118140960795 + 185362 * 2 ^ 59
def prefixEnd_185362 : Nat := 4983230072969 + 3 ^ 40 * 185362 * 2
def baseEnd_185362 : Nat := 84604267625608003575593

theorem tailTrace_185362 : CollatzResearch.WordTrace tailWord_185362 prefixEnd_185362 84604267625608003575593 := by
  unfold tailWord_185362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690176888618151538585585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4507138369648404102894893 1690176888618151538585585)
  ·
    refine ⟨1267632666463613653939189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1690176888618151538585585 1267632666463613653939189)
    ·
      refine ⟨118840562480963780056799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1267632666463613653939189 118840562480963780056799)
      ·
        refine ⟨178260843721445670085199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118840562480963780056799 178260843721445670085199)
        ·
          refine ⟨267391265582168505127799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178260843721445670085199 267391265582168505127799)
          ·
            refine ⟨401086898373252757691699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267391265582168505127799 401086898373252757691699)
            ·
              refine ⟨601630347559879136537549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401086898373252757691699 601630347559879136537549)
              ·
                refine ⟨225611380334954676201581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 601630347559879136537549 225611380334954676201581)
                ·
                  refine ⟨84604267625608003575593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225611380334954676201581 84604267625608003575593)
                  ·
                    rfl

theorem cell20_185362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_185362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185362 prefixEnd_185362 := by exact prefixLift 185362
  have htrace : WordTrace (prefixWord ++ tailWord_185362) baseStart_185362 baseEnd_185362 := by
    simpa [prefixWord, tailWord_185362, baseEnd_185362] using wordTrace_append hprefix tailTrace_185362
  have hstable : (prefixWord ++ tailWord_185362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185362).length < 2 ^ (prefixWord ++ tailWord_185362).sum := by decide
  have hdescent : baseEnd_185362 < baseStart_185362 := by decide
  rcases family_descends (prefixWord ++ tailWord_185362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185439 : List Nat := [1, 1, 2, 3, 1, 1, 7, 4]
def baseStart_185439 : Nat := 118140960795 + 185439 * 2 ^ 59
def prefixEnd_185439 : Nat := 4983230072969 + 3 ^ 40 * 185439 * 2
def baseEnd_185439 : Nat := 28213137507912652669537

theorem tailTrace_185439 : CollatzResearch.WordTrace tailWord_185439 prefixEnd_185439 28213137507912652669537 := by
  unfold tailWord_185439
  simp only [CollatzResearch.WordTrace]
  refine ⟨6763515975193648304895371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4509010650129098869930247 6763515975193648304895371)
  ·
    refine ⟨10145273962790472457343057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6763515975193648304895371 10145273962790472457343057)
    ·
      refine ⟨7608955472092854343007293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10145273962790472457343057 7608955472092854343007293)
      ·
        refine ⟨2853358302034820378627735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7608955472092854343007293 2853358302034820378627735)
        ·
          refine ⟨4280037453052230567941603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853358302034820378627735 4280037453052230567941603)
          ·
            refine ⟨6420056179578345851912405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4280037453052230567941603 6420056179578345851912405)
            ·
              refine ⟨150470066708867480904197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6420056179578345851912405 150470066708867480904197)
              ·
                refine ⟨28213137507912652669537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150470066708867480904197 28213137507912652669537)
                ·
                  rfl

theorem cell20_185439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 4].length) (baseStart_185439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185439 prefixEnd_185439 := by exact prefixLift 185439
  have htrace : WordTrace (prefixWord ++ tailWord_185439) baseStart_185439 baseEnd_185439 := by
    simpa [prefixWord, tailWord_185439, baseEnd_185439] using wordTrace_append hprefix tailTrace_185439
  have hstable : (prefixWord ++ tailWord_185439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185439).length < 2 ^ (prefixWord ++ tailWord_185439).sum := by decide
  have hdescent : baseEnd_185439 < baseStart_185439 := by decide
  rcases family_descends (prefixWord ++ tailWord_185439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185449 : List Nat := [1, 2, 1, 1, 1, 7, 2, 3, 2]
def baseStart_185449 : Nat := 118140960795 + 185449 * 2 ^ 59
def prefixEnd_185449 : Nat := 4983230072969 + 3 ^ 40 * 185449 * 2
def baseEnd_185449 : Nat := 84643976796222367675237

theorem tailTrace_185449 : CollatzResearch.WordTrace tailWord_185449 prefixEnd_185449 84643976796222367675237 := by
  unfold tailWord_185449
  simp only [CollatzResearch.WordTrace]
  refine ⟨6763880705157420012759401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4509253803438280008506267 6763880705157420012759401)
  ·
    refine ⟨5072910528868065009569551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6763880705157420012759401 5072910528868065009569551)
    ·
      refine ⟨7609365793302097514354327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5072910528868065009569551 7609365793302097514354327)
      ·
        refine ⟨11414048689953146271531491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7609365793302097514354327 11414048689953146271531491)
        ·
          refine ⟨17121073034929719407297237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11414048689953146271531491 17121073034929719407297237)
          ·
            refine ⟨401275149256165298608529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17121073034929719407297237 401275149256165298608529)
            ·
              refine ⟨300956361942123973956397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401275149256165298608529 300956361942123973956397)
              ·
                refine ⟨112858635728296490233649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300956361942123973956397 112858635728296490233649)
                ·
                  refine ⟨84643976796222367675237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112858635728296490233649 84643976796222367675237)
                  ·
                    rfl

theorem cell20_185449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 2].length) (baseStart_185449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185449 prefixEnd_185449 := by exact prefixLift 185449
  have htrace : WordTrace (prefixWord ++ tailWord_185449) baseStart_185449 baseEnd_185449 := by
    simpa [prefixWord, tailWord_185449, baseEnd_185449] using wordTrace_append hprefix tailTrace_185449
  have hstable : (prefixWord ++ tailWord_185449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185449).length < 2 ^ (prefixWord ++ tailWord_185449).sum := by decide
  have hdescent : baseEnd_185449 < baseStart_185449 := by decide
  rcases family_descends (prefixWord ++ tailWord_185449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185484 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 3]
def baseStart_185484 : Nat := 118140960795 + 185484 * 2 ^ 59
def prefixEnd_185484 : Nat := 4983230072969 + 3 ^ 40 * 185484 * 2
def baseEnd_185484 : Nat := 84659951749917801508427

theorem tailTrace_185484 : CollatzResearch.WordTrace tailWord_185484 prefixEnd_185484 84659951749917801508427 := by
  unfold tailWord_185484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382578630015310495141753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4510104840020413993522337 3382578630015310495141753)
  ·
    refine ⟨2536933972511482871356315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3382578630015310495141753 2536933972511482871356315)
    ·
      refine ⟨3805400958767224307034473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2536933972511482871356315 3805400958767224307034473)
      ·
        refine ⟨2854050719075418230275855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3805400958767224307034473 2854050719075418230275855)
        ·
          refine ⟨4281076078613127345413783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2854050719075418230275855 4281076078613127345413783)
          ·
            refine ⟨6421614117919691018120675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281076078613127345413783 6421614117919691018120675)
            ·
              refine ⟨9632421176879536527181013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6421614117919691018120675 9632421176879536527181013)
              ·
                refine ⟨225759871333114137355805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9632421176879536527181013 225759871333114137355805)
                ·
                  refine ⟨84659951749917801508427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225759871333114137355805 84659951749917801508427)
                  ·
                    rfl

theorem cell20_185484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_185484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185484 prefixEnd_185484 := by exact prefixLift 185484
  have htrace : WordTrace (prefixWord ++ tailWord_185484) baseStart_185484 baseEnd_185484 := by
    simpa [prefixWord, tailWord_185484, baseEnd_185484] using wordTrace_append hprefix tailTrace_185484
  have hstable : (prefixWord ++ tailWord_185484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185484).length < 2 ^ (prefixWord ++ tailWord_185484).sum := by decide
  have hdescent : baseEnd_185484 < baseStart_185484 := by decide
  rcases family_descends (prefixWord ++ tailWord_185484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185491 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 4]
def baseStart_185491 : Nat := 118140960795 + 185491 * 2 ^ 59
def prefixEnd_185491 : Nat := 4983230072969 + 3 ^ 40 * 185491 * 2
def baseEnd_185491 : Nat := 84663146740656888275065

theorem tailTrace_185491 : CollatzResearch.WordTrace tailWord_185491 prefixEnd_185491 84663146740656888275065 := by
  unfold tailWord_185491
  simp only [CollatzResearch.WordTrace]
  refine ⟨6765412571005261185788327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4510275047336840790525551 6765412571005261185788327)
  ·
    refine ⟨10148118856507891778682491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6765412571005261185788327 10148118856507891778682491)
    ·
      refine ⟨15222178284761837668023737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10148118856507891778682491 15222178284761837668023737)
      ·
        refine ⟨11416633713571378251017803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15222178284761837668023737 11416633713571378251017803)
        ·
          refine ⟨17124950570357067376526705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11416633713571378251017803 17124950570357067376526705)
          ·
            refine ⟨12843712927767800532395029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17124950570357067376526705 12843712927767800532395029)
            ·
              refine ⟨602049043489115649956017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12843712927767800532395029 602049043489115649956017)
              ·
                refine ⟨451536782616836737467013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602049043489115649956017 451536782616836737467013)
                ·
                  refine ⟨84663146740656888275065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 451536782616836737467013 84663146740656888275065)
                  ·
                    rfl

theorem cell20_185491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_185491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185491 prefixEnd_185491 := by exact prefixLift 185491
  have htrace : WordTrace (prefixWord ++ tailWord_185491) baseStart_185491 baseEnd_185491 := by
    simpa [prefixWord, tailWord_185491, baseEnd_185491] using wordTrace_append hprefix tailTrace_185491
  have hstable : (prefixWord ++ tailWord_185491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185491).length < 2 ^ (prefixWord ++ tailWord_185491).sum := by decide
  have hdescent : baseEnd_185491 < baseStart_185491 := by decide
  rcases family_descends (prefixWord ++ tailWord_185491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185522 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_185522 : Nat := 118140960795 + 185522 * 2 ^ 59
def prefixEnd_185522 : Nat := 4983230072969 + 3 ^ 40 * 185522 * 2
def baseEnd_185522 : Nat := 84677295985358558241605

theorem tailTrace_185522 : CollatzResearch.WordTrace tailWord_185522 prefixEnd_185522 84677295985358558241605 := by
  unfold tailWord_185522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1691635808473238370041705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4511028822595302320111213 1691635808473238370041705)
  ·
    refine ⟨1268726856354928777531279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1691635808473238370041705 1268726856354928777531279)
    ·
      refine ⟨1903090284532393166296919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1268726856354928777531279 1903090284532393166296919)
      ·
        refine ⟨2854635426798589749445379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1903090284532393166296919 2854635426798589749445379)
        ·
          refine ⟨4281953140197884624168069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2854635426798589749445379 4281953140197884624168069)
          ·
            refine ⟨802866213787103367031513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4281953140197884624168069 802866213787103367031513)
            ·
              refine ⟨602149660340327525273635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802866213787103367031513 602149660340327525273635)
              ·
                refine ⟨903224490510491287910453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602149660340327525273635 903224490510491287910453)
                ·
                  refine ⟨84677295985358558241605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 903224490510491287910453 84677295985358558241605)
                  ·
                    rfl

theorem cell20_185522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_185522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185522 prefixEnd_185522 := by exact prefixLift 185522
  have htrace : WordTrace (prefixWord ++ tailWord_185522) baseStart_185522 baseEnd_185522 := by
    simpa [prefixWord, tailWord_185522, baseEnd_185522] using wordTrace_append hprefix tailTrace_185522
  have hstable : (prefixWord ++ tailWord_185522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185522).length < 2 ^ (prefixWord ++ tailWord_185522).sum := by decide
  have hdescent : baseEnd_185522 < baseStart_185522 := by decide
  rcases family_descends (prefixWord ++ tailWord_185522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185580 : List Nat := [2, 2, 1, 1, 2, 6, 2, 2, 2]
def baseStart_185580 : Nat := 118140960795 + 185580 * 2 ^ 59
def prefixEnd_185580 : Nat := 4983230072969 + 3 ^ 40 * 185580 * 2
def baseEnd_185580 : Nat := 84703768765768134308035

theorem tailTrace_185580 : CollatzResearch.WordTrace tailWord_185580 prefixEnd_185580 84703768765768134308035 := by
  unfold tailWord_185580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3384329333841414692889097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4512439111788552923852129 3384329333841414692889097)
  ·
    refine ⟨2538247000381061019666823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3384329333841414692889097 2538247000381061019666823)
    ·
      refine ⟨3807370500571591529500235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2538247000381061019666823 3807370500571591529500235)
      ·
        refine ⟨5711055750857387294250353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3807370500571591529500235 5711055750857387294250353)
        ·
          refine ⟨4283291813143040470687765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5711055750857387294250353 4283291813143040470687765)
          ·
            refine ⟨200779303741080022063489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4283291813143040470687765 200779303741080022063489)
            ·
              refine ⟨150584477805810016547617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200779303741080022063489 150584477805810016547617)
              ·
                refine ⟨112938358354357512410713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150584477805810016547617 112938358354357512410713)
                ·
                  refine ⟨84703768765768134308035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112938358354357512410713 84703768765768134308035)
                  ·
                    rfl

theorem cell20_185580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_185580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185580 prefixEnd_185580 := by exact prefixLift 185580
  have htrace : WordTrace (prefixWord ++ tailWord_185580) baseStart_185580 baseEnd_185580 := by
    simpa [prefixWord, tailWord_185580, baseEnd_185580] using wordTrace_append hprefix tailTrace_185580
  have hstable : (prefixWord ++ tailWord_185580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185580).length < 2 ^ (prefixWord ++ tailWord_185580).sum := by decide
  have hdescent : baseEnd_185580 < baseStart_185580 := by decide
  rcases family_descends (prefixWord ++ tailWord_185580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185605 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 4]
def baseStart_185605 : Nat := 118140960795 + 185605 * 2 ^ 59
def prefixEnd_185605 : Nat := 4983230072969 + 3 ^ 40 * 185605 * 2
def baseEnd_185605 : Nat := 84715179446979158474599

theorem tailTrace_185605 : CollatzResearch.WordTrace tailWord_185605 prefixEnd_185605 84715179446979158474599 := by
  unfold tailWord_185605
  simp only [CollatzResearch.WordTrace]
  refine ⟨6769570492592258655438269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4513046995061505770292179 6769570492592258655438269)
  ·
    refine ⟨2538588934722096995789351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6769570492592258655438269 2538588934722096995789351)
    ·
      refine ⟨3807883402083145493684027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2538588934722096995789351 3807883402083145493684027)
      ·
        refine ⟨5711825103124718240526041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3807883402083145493684027 5711825103124718240526041)
        ·
          refine ⟨4283868827343538680394531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5711825103124718240526041 4283868827343538680394531)
          ·
            refine ⟨6425803241015308020591797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283868827343538680394531 6425803241015308020591797)
            ·
              refine ⟨602419053845185126930481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6425803241015308020591797 602419053845185126930481)
              ·
                refine ⟨451814290383888845197861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602419053845185126930481 451814290383888845197861)
                ·
                  refine ⟨84715179446979158474599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 451814290383888845197861 84715179446979158474599)
                  ·
                    rfl

theorem cell20_185605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_185605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185605 prefixEnd_185605 := by exact prefixLift 185605
  have htrace : WordTrace (prefixWord ++ tailWord_185605) baseStart_185605 baseEnd_185605 := by
    simpa [prefixWord, tailWord_185605, baseEnd_185605] using wordTrace_append hprefix tailTrace_185605
  have hstable : (prefixWord ++ tailWord_185605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185605).length < 2 ^ (prefixWord ++ tailWord_185605).sum := by decide
  have hdescent : baseEnd_185605 < baseStart_185605 := by decide
  rcases family_descends (prefixWord ++ tailWord_185605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185608 : List Nat := [2, 1, 3, 2, 4, 1, 3, 4]
def baseStart_185608 : Nat := 118140960795 + 185608 * 2 ^ 59
def prefixEnd_185608 : Nat := 4983230072969 + 3 ^ 40 * 185608 * 2
def baseEnd_185608 : Nat := 28238849576241493791529

theorem tailTrace_185608 : CollatzResearch.WordTrace tailWord_185608 prefixEnd_185608 28238849576241493791529 := by
  unfold tailWord_185608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3384839955790695083898739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4513119941054260111864985 3384839955790695083898739)
  ·
    refine ⟨5077259933686042625848109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3384839955790695083898739 5077259933686042625848109)
    ·
      refine ⟨1903972475132265984693041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5077259933686042625848109 1903972475132265984693041)
      ·
        refine ⟨1427979356349199488519781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1903972475132265984693041 1427979356349199488519781)
        ·
          refine ⟨267746129315474904097459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1427979356349199488519781 267746129315474904097459)
          ·
            refine ⟨401619193973212356146189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267746129315474904097459 401619193973212356146189)
            ·
              refine ⟨150607197739954633554821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401619193973212356146189 150607197739954633554821)
              ·
                refine ⟨28238849576241493791529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150607197739954633554821 28238849576241493791529)
                ·
                  rfl

theorem cell20_185608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_185608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185608 prefixEnd_185608 := by exact prefixLift 185608
  have htrace : WordTrace (prefixWord ++ tailWord_185608) baseStart_185608 baseEnd_185608 := by
    simpa [prefixWord, tailWord_185608, baseEnd_185608] using wordTrace_append hprefix tailTrace_185608
  have hstable : (prefixWord ++ tailWord_185608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185608).length < 2 ^ (prefixWord ++ tailWord_185608).sum := by decide
  have hdescent : baseEnd_185608 < baseStart_185608 := by decide
  rcases family_descends (prefixWord ++ tailWord_185608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185629 : List Nat := [1, 4, 2, 3, 1, 2, 7]
def baseStart_185629 : Nat := 118140960795 + 185629 * 2 ^ 59
def prefixEnd_185629 : Nat := 4983230072969 + 3 ^ 40 * 185629 * 2
def baseEnd_185629 : Nat := 9414014855660193519389

theorem tailTrace_185629 : CollatzResearch.WordTrace tailWord_185629 prefixEnd_185629 9414014855660193519389 := by
  unfold tailWord_185629
  simp only [CollatzResearch.WordTrace]
  refine ⟨6770445844505310754311941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4513630563003540502874627 6770445844505310754311941)
  ·
    refine ⟨1269458595844745766433489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6770445844505310754311941 1269458595844745766433489)
    ·
      refine ⟨952093946883559324825117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1269458595844745766433489 952093946883559324825117)
      ·
        refine ⟨357035230081334746809419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 952093946883559324825117 357035230081334746809419)
        ·
          refine ⟨535552845122002120214129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357035230081334746809419 535552845122002120214129)
          ·
            refine ⟨401664633841501590160597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535552845122002120214129 401664633841501590160597)
            ·
              refine ⟨9414014855660193519389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 401664633841501590160597 9414014855660193519389)
              ·
                rfl

theorem cell20_185629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 7].length) (baseStart_185629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185629 prefixEnd_185629 := by exact prefixLift 185629
  have htrace : WordTrace (prefixWord ++ tailWord_185629) baseStart_185629 baseEnd_185629 := by
    simpa [prefixWord, tailWord_185629, baseEnd_185629] using wordTrace_append hprefix tailTrace_185629
  have hstable : (prefixWord ++ tailWord_185629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185629).length < 2 ^ (prefixWord ++ tailWord_185629).sum := by decide
  have hdescent : baseEnd_185629 < baseStart_185629 := by decide
  rcases family_descends (prefixWord ++ tailWord_185629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185632 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 3]
def baseStart_185632 : Nat := 118140960795 + 185632 * 2 ^ 59
def prefixEnd_185632 : Nat := 4983230072969 + 3 ^ 40 * 185632 * 2
def baseEnd_185632 : Nat := 84727502982687064574489

theorem tailTrace_185632 : CollatzResearch.WordTrace tailWord_185632 prefixEnd_185632 84727502982687064574489 := by
  unfold tailWord_185632
  simp only [CollatzResearch.WordTrace]
  refine ⟨3385277631747221133335575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4513703508996294844447433 3385277631747221133335575)
  ·
    refine ⟨5077916447620831700003363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3385277631747221133335575 5077916447620831700003363)
    ·
      refine ⟨7616874671431247550005045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5077916447620831700003363 7616874671431247550005045)
      ·
        refine ⟨714082000446679457812973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7616874671431247550005045 714082000446679457812973)
        ·
          refine ⟨267780750167504796679865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 714082000446679457812973 267780750167504796679865)
          ·
            refine ⟨200835562625628597509899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267780750167504796679865 200835562625628597509899)
            ·
              refine ⟨301253343938442896264849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200835562625628597509899 301253343938442896264849)
              ·
                refine ⟨225940007953832172198637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301253343938442896264849 225940007953832172198637)
                ·
                  refine ⟨84727502982687064574489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225940007953832172198637 84727502982687064574489)
                  ·
                    rfl

theorem cell20_185632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_185632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185632 prefixEnd_185632 := by exact prefixLift 185632
  have htrace : WordTrace (prefixWord ++ tailWord_185632) baseStart_185632 baseEnd_185632 := by
    simpa [prefixWord, tailWord_185632, baseEnd_185632] using wordTrace_append hprefix tailTrace_185632
  have hstable : (prefixWord ++ tailWord_185632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185632).length < 2 ^ (prefixWord ++ tailWord_185632).sum := by decide
  have hdescent : baseEnd_185632 < baseStart_185632 := by decide
  rcases family_descends (prefixWord ++ tailWord_185632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185636 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_185636 : Nat := 118140960795 + 185636 * 2 ^ 59
def prefixEnd_185636 : Nat := 4983230072969 + 3 ^ 40 * 185636 * 2
def baseEnd_185636 : Nat := 84729328691680828441139

theorem tailTrace_185636 : CollatzResearch.WordTrace tailWord_185636 prefixEnd_185636 84729328691680828441139 := by
  unfold tailWord_185636
  simp only [CollatzResearch.WordTrace]
  refine ⟨3385350577739975474908381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4513800770319967299877841 3385350577739975474908381)
  ·
    refine ⟨1269506466652490803090643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3385350577739975474908381 1269506466652490803090643)
    ·
      refine ⟨1904259699978736204635965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1269506466652490803090643 1904259699978736204635965)
      ·
        refine ⟨714097387492026076738487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1904259699978736204635965 714097387492026076738487)
        ·
          refine ⟨1071146081238039115107731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714097387492026076738487 1071146081238039115107731)
          ·
            refine ⟨1606719121857058672661597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071146081238039115107731 1606719121857058672661597)
            ·
              refine ⟨602519670696397002248099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1606719121857058672661597 602519670696397002248099)
              ·
                refine ⟨903779506044595503372149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602519670696397002248099 903779506044595503372149)
                ·
                  refine ⟨84729328691680828441139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 903779506044595503372149 84729328691680828441139)
                  ·
                    rfl

theorem cell20_185636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_185636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185636 prefixEnd_185636 := by exact prefixLift 185636
  have htrace : WordTrace (prefixWord ++ tailWord_185636) baseStart_185636 baseEnd_185636 := by
    simpa [prefixWord, tailWord_185636, baseEnd_185636] using wordTrace_append hprefix tailTrace_185636
  have hstable : (prefixWord ++ tailWord_185636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185636).length < 2 ^ (prefixWord ++ tailWord_185636).sum := by decide
  have hdescent : baseEnd_185636 < baseStart_185636 := by decide
  rcases family_descends (prefixWord ++ tailWord_185636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185708 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 3]
def baseStart_185708 : Nat := 118140960795 + 185708 * 2 ^ 59
def prefixEnd_185708 : Nat := 4983230072969 + 3 ^ 40 * 185708 * 2
def baseEnd_185708 : Nat := 84762191453568578040845

theorem tailTrace_185708 : CollatzResearch.WordTrace tailWord_185708 prefixEnd_185708 84762191453568578040845 := by
  unfold tailWord_185708
  simp only [CollatzResearch.WordTrace]
  refine ⟨3386663605609553623218889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4515551474146071497625185 3386663605609553623218889)
  ·
    refine ⟨2539997704207165217414167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3386663605609553623218889 2539997704207165217414167)
    ·
      refine ⟨3809996556310747826121251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2539997704207165217414167 3809996556310747826121251)
      ·
        refine ⟨5714994834466121739181877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3809996556310747826121251 5714994834466121739181877)
        ·
          refine ⟨535780765731198913048301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5714994834466121739181877 535780765731198913048301)
          ·
            refine ⟨200917787149199592393113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 535780765731198913048301 200917787149199592393113)
            ·
              refine ⟨150688340361899694294835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200917787149199592393113 150688340361899694294835)
              ·
                refine ⟨226032510542849541442253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150688340361899694294835 226032510542849541442253)
                ·
                  refine ⟨84762191453568578040845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226032510542849541442253 84762191453568578040845)
                  ·
                    rfl

theorem cell20_185708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_185708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185708 prefixEnd_185708 := by exact prefixLift 185708
  have htrace : WordTrace (prefixWord ++ tailWord_185708) baseStart_185708 baseEnd_185708 := by
    simpa [prefixWord, tailWord_185708, baseEnd_185708] using wordTrace_append hprefix tailTrace_185708
  have hstable : (prefixWord ++ tailWord_185708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185708).length < 2 ^ (prefixWord ++ tailWord_185708).sum := by decide
  have hdescent : baseEnd_185708 < baseStart_185708 := by decide
  rcases family_descends (prefixWord ++ tailWord_185708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185712 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 3]
def baseStart_185712 : Nat := 118140960795 + 185712 * 2 ^ 59
def prefixEnd_185712 : Nat := 4983230072969 + 3 ^ 40 * 185712 * 2
def baseEnd_185712 : Nat := 84764017162562341907495

theorem tailTrace_185712 : CollatzResearch.WordTrace tailWord_185712 prefixEnd_185712 84764017162562341907495 := by
  unfold tailWord_185712
  simp only [CollatzResearch.WordTrace]
  refine ⟨3386736551602307964791695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4515648735469743953055593 3386736551602307964791695)
  ·
    refine ⟨5080104827403461947187543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3386736551602307964791695 5080104827403461947187543)
    ·
      refine ⟨7620157241105192920781315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5080104827403461947187543 7620157241105192920781315)
      ·
        refine ⟨11430235861657789381171973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7620157241105192920781315 11430235861657789381171973)
        ·
          refine ⟨2143169224060835508969745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11430235861657789381171973 2143169224060835508969745)
          ·
            refine ⟨1607376918045626631727309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2143169224060835508969745 1607376918045626631727309)
            ·
              refine ⟨602766344267109986897741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1607376918045626631727309 602766344267109986897741)
              ·
                refine ⟨226037379100166245086653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 602766344267109986897741 226037379100166245086653)
                ·
                  refine ⟨84764017162562341907495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226037379100166245086653 84764017162562341907495)
                  ·
                    rfl

theorem cell20_185712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_185712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185712 prefixEnd_185712 := by exact prefixLift 185712
  have htrace : WordTrace (prefixWord ++ tailWord_185712) baseStart_185712 baseEnd_185712 := by
    simpa [prefixWord, tailWord_185712, baseEnd_185712] using wordTrace_append hprefix tailTrace_185712
  have hstable : (prefixWord ++ tailWord_185712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185712).length < 2 ^ (prefixWord ++ tailWord_185712).sum := by decide
  have hdescent : baseEnd_185712 < baseStart_185712 := by decide
  rcases family_descends (prefixWord ++ tailWord_185712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185733 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_185733 : Nat := 118140960795 + 185733 * 2 ^ 59
def prefixEnd_185733 : Nat := 4983230072969 + 3 ^ 40 * 185733 * 2
def baseEnd_185733 : Nat := 84773602134779602207409

theorem tailTrace_185733 : CollatzResearch.WordTrace tailWord_185733 prefixEnd_185733 84773602134779602207409 := by
  unfold tailWord_185733
  simp only [CollatzResearch.WordTrace]
  refine ⟨6774239036128536516097853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4516159357419024344065235 6774239036128536516097853)
  ·
    refine ⟨2540339638548201193536695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6774239036128536516097853 2540339638548201193536695)
    ·
      refine ⟨3810509457822301790305043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2540339638548201193536695 3810509457822301790305043)
      ·
        refine ⟨5715764186733452685457565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3810509457822301790305043 5715764186733452685457565)
        ·
          refine ⟨2143411570025044757046587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5715764186733452685457565 2143411570025044757046587)
          ·
            refine ⟨3215117355037567135569881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143411570025044757046587 3215117355037567135569881)
            ·
              refine ⟨2411338016278175351677411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3215117355037567135569881 2411338016278175351677411)
              ·
                refine ⟨3617007024417263027516117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411338016278175351677411 3617007024417263027516117)
                ·
                  refine ⟨84773602134779602207409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3617007024417263027516117 84773602134779602207409)
                  ·
                    rfl

theorem cell20_185733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_185733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185733 prefixEnd_185733 := by exact prefixLift 185733
  have htrace : WordTrace (prefixWord ++ tailWord_185733) baseStart_185733 baseEnd_185733 := by
    simpa [prefixWord, tailWord_185733, baseEnd_185733] using wordTrace_append hprefix tailTrace_185733
  have hstable : (prefixWord ++ tailWord_185733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185733).length < 2 ^ (prefixWord ++ tailWord_185733).sum := by decide
  have hdescent : baseEnd_185733 < baseStart_185733 := by decide
  rcases family_descends (prefixWord ++ tailWord_185733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185753 : List Nat := [1, 2, 1, 2, 1, 5, 4, 2, 2]
def baseStart_185753 : Nat := 118140960795 + 185753 * 2 ^ 59
def prefixEnd_185753 : Nat := 4983230072969 + 3 ^ 40 * 185753 * 2
def baseEnd_185753 : Nat := 84782730679748421540661

theorem tailTrace_185753 : CollatzResearch.WordTrace tailWord_185753 prefixEnd_185753 84782730679748421540661 := by
  unfold tailWord_185753
  simp only [CollatzResearch.WordTrace]
  refine ⟨6774968496056079931825913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4516645664037386621217275 6774968496056079931825913)
  ·
    refine ⟨5081226372042059948869435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6774968496056079931825913 5081226372042059948869435)
    ·
      refine ⟨7621839558063089923304153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5081226372042059948869435 7621839558063089923304153)
      ·
        refine ⟨5716379668547317442478115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7621839558063089923304153 5716379668547317442478115)
        ·
          refine ⟨8574569502820976163717173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5716379668547317442478115 8574569502820976163717173)
          ·
            refine ⟨803865890889466515348485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8574569502820976163717173 803865890889466515348485)
            ·
              refine ⟨150724854541774971627841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 803865890889466515348485 150724854541774971627841)
              ·
                refine ⟨113043640906331228720881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150724854541774971627841 113043640906331228720881)
                ·
                  refine ⟨84782730679748421540661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113043640906331228720881 84782730679748421540661)
                  ·
                    rfl

theorem cell20_185753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 2].length) (baseStart_185753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185753 prefixEnd_185753 := by exact prefixLift 185753
  have htrace : WordTrace (prefixWord ++ tailWord_185753) baseStart_185753 baseEnd_185753 := by
    simpa [prefixWord, tailWord_185753, baseEnd_185753] using wordTrace_append hprefix tailTrace_185753
  have hstable : (prefixWord ++ tailWord_185753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185753).length < 2 ^ (prefixWord ++ tailWord_185753).sum := by decide
  have hdescent : baseEnd_185753 < baseStart_185753 := by decide
  rcases family_descends (prefixWord ++ tailWord_185753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185794 : List Nat := [3, 5, 2, 1, 1, 1, 7]
def baseStart_185794 : Nat := 118140960795 + 185794 * 2 ^ 59
def prefixEnd_185794 : Nat := 4983230072969 + 3 ^ 40 * 185794 * 2
def baseEnd_185794 : Nat := 9422382688548277908203

theorem tailTrace_185794 : CollatzResearch.WordTrace tailWord_185794 prefixEnd_185794 9422382688548277908203 := by
  unfold tailWord_185794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694115972226885983517109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4517642592605029289378957 1694115972226885983517109)
  ·
    refine ⟨158823372396270560954729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1694115972226885983517109 158823372396270560954729)
    ·
      refine ⟨119117529297202920716047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158823372396270560954729 119117529297202920716047)
      ·
        refine ⟨178676293945804381074071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119117529297202920716047 178676293945804381074071)
        ·
          refine ⟨268014440918706571611107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178676293945804381074071 268014440918706571611107)
          ·
            refine ⟨402021661378059857416661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268014440918706571611107 402021661378059857416661)
            ·
              refine ⟨9422382688548277908203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 402021661378059857416661 9422382688548277908203)
              ·
                rfl

theorem cell20_185794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 7].length) (baseStart_185794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185794 prefixEnd_185794 := by exact prefixLift 185794
  have htrace : WordTrace (prefixWord ++ tailWord_185794) baseStart_185794 baseEnd_185794 := by
    simpa [prefixWord, tailWord_185794, baseEnd_185794] using wordTrace_append hprefix tailTrace_185794
  have hstable : (prefixWord ++ tailWord_185794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185794).length < 2 ^ (prefixWord ++ tailWord_185794).sum := by decide
  have hdescent : baseEnd_185794 < baseStart_185794 := by decide
  rcases family_descends (prefixWord ++ tailWord_185794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185802 : List Nat := [3, 1, 2, 1, 2, 4, 7]
def baseStart_185802 : Nat := 118140960795 + 185802 * 2 ^ 59
def prefixEnd_185802 : Nat := 4983230072969 + 3 ^ 40 * 185802 * 2
def baseEnd_185802 : Nat := 9422788401658003211903

theorem tailTrace_185802 : CollatzResearch.WordTrace tailWord_185802 prefixEnd_185802 9422788401658003211903 := by
  unfold tailWord_185802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694188918219640325089915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4517837115252374200239773 1694188918219640325089915)
  ·
    refine ⟨2541283377329460487634873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1694188918219640325089915 2541283377329460487634873)
    ·
      refine ⟨1905962532997095365726155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2541283377329460487634873 1905962532997095365726155)
      ·
        refine ⟨2858943799495643048589233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905962532997095365726155 2858943799495643048589233)
        ·
          refine ⟨2144207849621732286441925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2858943799495643048589233 2144207849621732286441925)
          ·
            refine ⟨402038971804074803707861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2144207849621732286441925 402038971804074803707861)
            ·
              refine ⟨9422788401658003211903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 402038971804074803707861 9422788401658003211903)
              ·
                rfl

theorem cell20_185802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 7].length) (baseStart_185802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185802 prefixEnd_185802 := by exact prefixLift 185802
  have htrace : WordTrace (prefixWord ++ tailWord_185802) baseStart_185802 baseEnd_185802 := by
    simpa [prefixWord, tailWord_185802, baseEnd_185802] using wordTrace_append hprefix tailTrace_185802
  have hstable : (prefixWord ++ tailWord_185802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185802).length < 2 ^ (prefixWord ++ tailWord_185802).sum := by decide
  have hdescent : baseEnd_185802 < baseStart_185802 := by decide
  rcases family_descends (prefixWord ++ tailWord_185802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185840 : List Nat := [2, 1, 1, 1, 3, 5, 1, 6]
def baseStart_185840 : Nat := 118140960795 + 185840 * 2 ^ 59
def prefixEnd_185840 : Nat := 4983230072969 + 3 ^ 40 * 185840 * 2
def baseEnd_185840 : Nat := 28274146616787595213435

theorem tailTrace_185840 : CollatzResearch.WordTrace tailWord_185840 prefixEnd_185840 28274146616787595213435 := by
  unfold tailWord_185840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389070823370446895121487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4518761097827262526828649 3389070823370446895121487)
  ·
    refine ⟨5083606235055670342682231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3389070823370446895121487 5083606235055670342682231)
    ·
      refine ⟨7625409352583505514023347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5083606235055670342682231 7625409352583505514023347)
      ·
        refine ⟨11438114028875258271035021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7625409352583505514023347 11438114028875258271035021)
        ·
          refine ⟨4289292760828221851638133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11438114028875258271035021 4289292760828221851638133)
          ·
            refine ⟨402121196327645798591075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4289292760828221851638133 402121196327645798591075)
            ·
              refine ⟨603181794491468697886613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402121196327645798591075 603181794491468697886613)
              ·
                refine ⟨28274146616787595213435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 603181794491468697886613 28274146616787595213435)
                ·
                  rfl

theorem cell20_185840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_185840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185840 prefixEnd_185840 := by exact prefixLift 185840
  have htrace : WordTrace (prefixWord ++ tailWord_185840) baseStart_185840 baseEnd_185840 := by
    simpa [prefixWord, tailWord_185840, baseEnd_185840] using wordTrace_append hprefix tailTrace_185840
  have hstable : (prefixWord ++ tailWord_185840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185840).length < 2 ^ (prefixWord ++ tailWord_185840).sum := by decide
  have hdescent : baseEnd_185840 < baseStart_185840 := by decide
  rcases family_descends (prefixWord ++ tailWord_185840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185846 : List Nat := [5, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_185846 : Nat := 118140960795 + 185846 * 2 ^ 59
def prefixEnd_185846 : Nat := 4983230072969 + 3 ^ 40 * 185846 * 2
def baseEnd_185846 : Nat := 84825178413853431440281

theorem tailTrace_185846 : CollatzResearch.WordTrace tailWord_185846 prefixEnd_185846 84825178413853431440281 := by
  unfold tailWord_185846
  simp only [CollatzResearch.WordTrace]
  refine ⟨423647530294947300935087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4518906989812771209974261 423647530294947300935087)
  ·
    refine ⟨635471295442420951402631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 423647530294947300935087 635471295442420951402631)
    ·
      refine ⟨953206943163631427103947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635471295442420951402631 953206943163631427103947)
      ·
        refine ⟨1429810414745447140655921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953206943163631427103947 1429810414745447140655921)
        ·
          refine ⟨1072357811059085355491941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1429810414745447140655921 1072357811059085355491941)
          ·
            refine ⟨201067089573578504154739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1072357811059085355491941 201067089573578504154739)
            ·
              refine ⟨301600634360367756232109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201067089573578504154739 301600634360367756232109)
              ·
                refine ⟨113100237885137908587041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301600634360367756232109 113100237885137908587041)
                ·
                  refine ⟨84825178413853431440281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113100237885137908587041 84825178413853431440281)
                  ·
                    rfl

theorem cell20_185846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_185846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185846 prefixEnd_185846 := by exact prefixLift 185846
  have htrace : WordTrace (prefixWord ++ tailWord_185846) baseStart_185846 baseEnd_185846 := by
    simpa [prefixWord, tailWord_185846, baseEnd_185846] using wordTrace_append hprefix tailTrace_185846
  have hstable : (prefixWord ++ tailWord_185846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185846).length < 2 ^ (prefixWord ++ tailWord_185846).sum := by decide
  have hdescent : baseEnd_185846 < baseStart_185846 := by decide
  rcases family_descends (prefixWord ++ tailWord_185846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185857 : List Nat := [1, 2, 4, 1, 4, 2, 6]
def baseStart_185857 : Nat := 118140960795 + 185857 * 2 ^ 59
def prefixEnd_185857 : Nat := 4983230072969 + 3 ^ 40 * 185857 * 2
def baseEnd_185857 : Nat := 9425577679287364674841

theorem tailTrace_185857 : CollatzResearch.WordTrace tailWord_185857 prefixEnd_185857 9425577679287364674841 := by
  unfold tailWord_185857
  simp only [CollatzResearch.WordTrace]
  refine ⟨6778761687679305693611825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4519174458452870462407883 6778761687679305693611825)
  ·
    refine ⟨5084071265759479270208869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6778761687679305693611825 5084071265759479270208869)
    ·
      refine ⟨953263362329902363164163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5084071265759479270208869 953263362329902363164163)
      ·
        refine ⟨1429895043494853544746245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953263362329902363164163 1429895043494853544746245)
        ·
          refine ⟨268105320655285039639921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1429895043494853544746245 268105320655285039639921)
          ·
            refine ⟨201078990491463779729941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268105320655285039639921 201078990491463779729941)
            ·
              refine ⟨9425577679287364674841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 201078990491463779729941 9425577679287364674841)
              ·
                rfl

theorem cell20_185857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 6].length) (baseStart_185857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185857 prefixEnd_185857 := by exact prefixLift 185857
  have htrace : WordTrace (prefixWord ++ tailWord_185857) baseStart_185857 baseEnd_185857 := by
    simpa [prefixWord, tailWord_185857, baseEnd_185857] using wordTrace_append hprefix tailTrace_185857
  have hstable : (prefixWord ++ tailWord_185857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185857).length < 2 ^ (prefixWord ++ tailWord_185857).sum := by decide
  have hdescent : baseEnd_185857 < baseStart_185857 := by decide
  rcases family_descends (prefixWord ++ tailWord_185857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185867 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 4]
def baseStart_185867 : Nat := 118140960795 + 185867 * 2 ^ 59
def prefixEnd_185867 : Nat := 4983230072969 + 3 ^ 40 * 185867 * 2
def baseEnd_185867 : Nat := 84834763386070691740195

theorem tailTrace_185867 : CollatzResearch.WordTrace tailWord_185867 prefixEnd_185867 84834763386070691740195 := by
  unfold tailWord_185867
  simp only [CollatzResearch.WordTrace]
  refine ⟨6779126417643077401475855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4519417611762051600983903 6779126417643077401475855)
  ·
    refine ⟨10168689626464616102213783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6779126417643077401475855 10168689626464616102213783)
    ·
      refine ⟨15253034439696924153320675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10168689626464616102213783 15253034439696924153320675)
      ·
        refine ⟨22879551659545386229981013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15253034439696924153320675 22879551659545386229981013)
        ·
          refine ⟨134059873005148747441295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 22879551659545386229981013 134059873005148747441295)
          ·
            refine ⟨201089809507723121161943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134059873005148747441295 201089809507723121161943)
            ·
              refine ⟨301634714261584681742915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201089809507723121161943 301634714261584681742915)
              ·
                refine ⟨452452071392377022614373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301634714261584681742915 452452071392377022614373)
                ·
                  refine ⟨84834763386070691740195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 452452071392377022614373 84834763386070691740195)
                  ·
                    rfl

theorem cell20_185867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 4].length) (baseStart_185867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185867 prefixEnd_185867 := by exact prefixLift 185867
  have htrace : WordTrace (prefixWord ++ tailWord_185867) baseStart_185867 baseEnd_185867 := by
    simpa [prefixWord, tailWord_185867, baseEnd_185867] using wordTrace_append hprefix tailTrace_185867
  have hstable : (prefixWord ++ tailWord_185867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185867).length < 2 ^ (prefixWord ++ tailWord_185867).sum := by decide
  have hdescent : baseEnd_185867 < baseStart_185867 := by decide
  rcases family_descends (prefixWord ++ tailWord_185867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185916 : List Nat := [2, 2, 2, 2, 4, 8]
def baseStart_185916 : Nat := 118140960795 + 185916 * 2 ^ 59
def prefixEnd_185916 : Nat := 4983230072969 + 3 ^ 40 * 185916 * 2
def baseEnd_185916 : Nat := 3142856604490529596543

theorem tailTrace_185916 : CollatzResearch.WordTrace tailWord_185916 prefixEnd_185916 3142856604490529596543 := by
  unfold tailWord_185916
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390456797232779385004801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4520609062977039180006401 3390456797232779385004801)
  ·
    refine ⟨2542842597924584538753601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3390456797232779385004801 2542842597924584538753601)
    ·
      refine ⟨1907131948443438404065201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2542842597924584538753601 1907131948443438404065201)
      ·
        refine ⟨1430348961332578803048901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1907131948443438404065201 1430348961332578803048901)
        ·
          refine ⟨268190430249858525571669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1430348961332578803048901 268190430249858525571669)
          ·
            refine ⟨3142856604490529596543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 268190430249858525571669 3142856604490529596543)
            ·
              rfl

theorem cell20_185916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 8].length) (baseStart_185916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185916 prefixEnd_185916 := by exact prefixLift 185916
  have htrace : WordTrace (prefixWord ++ tailWord_185916) baseStart_185916 baseEnd_185916 := by
    simpa [prefixWord, tailWord_185916, baseEnd_185916] using wordTrace_append hprefix tailTrace_185916
  have hstable : (prefixWord ++ tailWord_185916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185916).length < 2 ^ (prefixWord ++ tailWord_185916).sum := by decide
  have hdescent : baseEnd_185916 < baseStart_185916 := by decide
  rcases family_descends (prefixWord ++ tailWord_185916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185940 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 3]
def baseStart_185940 : Nat := 118140960795 + 185940 * 2 ^ 59
def prefixEnd_185940 : Nat := 4983230072969 + 3 ^ 40 * 185940 * 2
def baseEnd_185940 : Nat := 84868082575206882306563

theorem tailTrace_185940 : CollatzResearch.WordTrace tailWord_185940 prefixEnd_185940 84868082575206882306563 := by
  unfold tailWord_185940
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390894473189305434441637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4521192630919073912588849 3390894473189305434441637)
  ·
    refine ⟨635792713722994768957807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3390894473189305434441637 635792713722994768957807)
    ·
      refine ⟨953689070584492153436711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635792713722994768957807 953689070584492153436711)
      ·
        refine ⟨1430533605876738230155067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953689070584492153436711 1430533605876738230155067)
        ·
          refine ⟨2145800408815107345232601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430533605876738230155067 2145800408815107345232601)
          ·
            refine ⟨1609350306611330508924451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2145800408815107345232601 1609350306611330508924451)
            ·
              refine ⟨2414025459916995763386677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609350306611330508924451 2414025459916995763386677)
              ·
                refine ⟨226314886867218352817501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2414025459916995763386677 226314886867218352817501)
                ·
                  refine ⟨84868082575206882306563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226314886867218352817501 84868082575206882306563)
                  ·
                    rfl

theorem cell20_185940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_185940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185940 prefixEnd_185940 := by exact prefixLift 185940
  have htrace : WordTrace (prefixWord ++ tailWord_185940) baseStart_185940 baseEnd_185940 := by
    simpa [prefixWord, tailWord_185940, baseEnd_185940] using wordTrace_append hprefix tailTrace_185940
  have hstable : (prefixWord ++ tailWord_185940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185940).length < 2 ^ (prefixWord ++ tailWord_185940).sum := by decide
  have hdescent : baseEnd_185940 < baseStart_185940 := by decide
  rcases family_descends (prefixWord ++ tailWord_185940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185974 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_185974 : Nat := 118140960795 + 185974 * 2 ^ 59
def prefixEnd_185974 : Nat := 4983230072969 + 3 ^ 40 * 185974 * 2
def baseEnd_185974 : Nat := 84883601101653875173091

theorem tailTrace_185974 : CollatzResearch.WordTrace tailWord_185974 prefixEnd_185974 84883601101653875173091 := by
  unfold tailWord_185974
  simp only [CollatzResearch.WordTrace]
  refine ⟨423939314265964667226311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4522019352170289783747317 423939314265964667226311)
  ·
    refine ⟨635908971398947000839467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 423939314265964667226311 635908971398947000839467)
    ·
      refine ⟨953863457098420501259201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635908971398947000839467 953863457098420501259201)
      ·
        refine ⟨715397592823815375944401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 953863457098420501259201 715397592823815375944401)
        ·
          refine ⟨536548194617861531958301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715397592823815375944401 536548194617861531958301)
          ·
            refine ⟨201205572981698074484363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 536548194617861531958301 201205572981698074484363)
            ·
              refine ⟨301808359472547111726545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201205572981698074484363 301808359472547111726545)
              ·
                refine ⟨226356269604410333794909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301808359472547111726545 226356269604410333794909)
                ·
                  refine ⟨84883601101653875173091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226356269604410333794909 84883601101653875173091)
                  ·
                    rfl

theorem cell20_185974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_185974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185974 prefixEnd_185974 := by exact prefixLift 185974
  have htrace : WordTrace (prefixWord ++ tailWord_185974) baseStart_185974 baseEnd_185974 := by
    simpa [prefixWord, tailWord_185974, baseEnd_185974] using wordTrace_append hprefix tailTrace_185974
  have hstable : (prefixWord ++ tailWord_185974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185974).length < 2 ^ (prefixWord ++ tailWord_185974).sum := by decide
  have hdescent : baseEnd_185974 < baseStart_185974 := by decide
  rcases family_descends (prefixWord ++ tailWord_185974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185985 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 4]
def baseStart_185985 : Nat := 118140960795 + 185985 * 2 ^ 59
def prefixEnd_185985 : Nat := 4983230072969 + 3 ^ 40 * 185985 * 2
def baseEnd_185985 : Nat := 84888621801386725806379

theorem tailTrace_185985 : CollatzResearch.WordTrace tailWord_185985 prefixEnd_185985 84888621801386725806379 := by
  unfold tailWord_185985
  simp only [CollatzResearch.WordTrace]
  refine ⟨6783430231215583554271409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4522286820810389036180939 6783430231215583554271409)
  ·
    refine ⟨5087572673411687665703557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6783430231215583554271409 5087572673411687665703557)
    ·
      refine ⟨953919876264691437319417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5087572673411687665703557 953919876264691437319417)
      ·
        refine ⟨715439907198518577989563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 953919876264691437319417 715439907198518577989563)
        ·
          refine ⟨1073159860797777866984345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715439907198518577989563 1073159860797777866984345)
          ·
            refine ⟨804869895598333400238259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073159860797777866984345 804869895598333400238259)
            ·
              refine ⟨1207304843397500100357389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804869895598333400238259 1207304843397500100357389)
              ·
                refine ⟨452739316274062537634021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1207304843397500100357389 452739316274062537634021)
                ·
                  refine ⟨84888621801386725806379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 452739316274062537634021 84888621801386725806379)
                  ·
                    rfl

theorem cell20_185985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_185985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_185985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_185985 prefixEnd_185985 := by exact prefixLift 185985
  have htrace : WordTrace (prefixWord ++ tailWord_185985) baseStart_185985 baseEnd_185985 := by
    simpa [prefixWord, tailWord_185985, baseEnd_185985] using wordTrace_append hprefix tailTrace_185985
  have hstable : (prefixWord ++ tailWord_185985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185985).length < 2 ^ (prefixWord ++ tailWord_185985).sum := by decide
  have hdescent : baseEnd_185985 < baseStart_185985 := by decide
  rcases family_descends (prefixWord ++ tailWord_185985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186015 : List Nat := [1, 1, 2, 7, 2, 1, 1, 3, 2]
def baseStart_186015 : Nat := 118140960795 + 186015 * 2 ^ 59
def prefixEnd_186015 : Nat := 4983230072969 + 3 ^ 40 * 186015 * 2
def baseEnd_186015 : Nat := 84902314618839954806257

theorem tailTrace_186015 : CollatzResearch.WordTrace tailWord_186015 prefixEnd_186015 84902314618839954806257 := by
  unfold tailWord_186015
  simp only [CollatzResearch.WordTrace]
  refine ⟨6784524421106898677863499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4523016280737932451908999 6784524421106898677863499)
  ·
    refine ⟨10176786631660348016795249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6784524421106898677863499 10176786631660348016795249)
    ·
      refine ⟨7632589973745261012596437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10176786631660348016795249 7632589973745261012596437)
      ·
        refine ⟨178888827509654554982729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 7632589973745261012596437 178888827509654554982729)
        ·
          refine ⟨134166620632240916237047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178888827509654554982729 134166620632240916237047)
          ·
            refine ⟨201249930948361374355571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134166620632240916237047 201249930948361374355571)
            ·
              refine ⟨301874896422542061533357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201249930948361374355571 301874896422542061533357)
              ·
                refine ⟨113203086158453273075009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301874896422542061533357 113203086158453273075009)
                ·
                  refine ⟨84902314618839954806257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113203086158453273075009 84902314618839954806257)
                  ·
                    rfl

theorem cell20_186015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 2].length) (baseStart_186015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186015 prefixEnd_186015 := by exact prefixLift 186015
  have htrace : WordTrace (prefixWord ++ tailWord_186015) baseStart_186015 baseEnd_186015 := by
    simpa [prefixWord, tailWord_186015, baseEnd_186015] using wordTrace_append hprefix tailTrace_186015
  have hstable : (prefixWord ++ tailWord_186015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186015).length < 2 ^ (prefixWord ++ tailWord_186015).sum := by decide
  have hdescent : baseEnd_186015 < baseStart_186015 := by decide
  rcases family_descends (prefixWord ++ tailWord_186015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186164 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 3]
def baseStart_186164 : Nat := 118140960795 + 186164 * 2 ^ 59
def prefixEnd_186164 : Nat := 4983230072969 + 3 ^ 40 * 186164 * 2
def baseEnd_186164 : Nat := 84970322278857658838981

theorem tailTrace_186164 : CollatzResearch.WordTrace tailWord_186164 prefixEnd_186164 84970322278857658838981 := by
  unfold tailWord_186164
  simp only [CollatzResearch.WordTrace]
  refine ⟨3394979448783548562518773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4526639265044731416691697 3394979448783548562518773)
  ·
    refine ⟨318279323323457677736135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3394979448783548562518773 318279323323457677736135)
    ·
      refine ⟨477418984985186516604203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318279323323457677736135 477418984985186516604203)
      ·
        refine ⟨716128477477779774906305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477418984985186516604203 716128477477779774906305)
        ·
          refine ⟨537096358108334831179729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716128477477779774906305 537096358108334831179729)
          ·
            refine ⟨402822268581251123384797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537096358108334831179729 402822268581251123384797)
            ·
              refine ⟨151058350717969171269299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 402822268581251123384797 151058350717969171269299)
              ·
                refine ⟨226587526076953756903949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151058350717969171269299 226587526076953756903949)
                ·
                  refine ⟨84970322278857658838981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226587526076953756903949 84970322278857658838981)
                  ·
                    rfl

theorem cell20_186164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_186164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186164 prefixEnd_186164 := by exact prefixLift 186164
  have htrace : WordTrace (prefixWord ++ tailWord_186164) baseStart_186164 baseEnd_186164 := by
    simpa [prefixWord, tailWord_186164, baseEnd_186164] using wordTrace_append hprefix tailTrace_186164
  have hstable : (prefixWord ++ tailWord_186164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186164).length < 2 ^ (prefixWord ++ tailWord_186164).sum := by decide
  have hdescent : baseEnd_186164 < baseStart_186164 := by decide
  rcases family_descends (prefixWord ++ tailWord_186164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186188 : List Nat := [2, 2, 1, 3, 5, 1, 1, 3, 2]
def baseStart_186188 : Nat := 118140960795 + 186188 * 2 ^ 59
def prefixEnd_186188 : Nat := 4983230072969 + 3 ^ 40 * 186188 * 2
def baseEnd_186188 : Nat := 84981276532820242038883

theorem tailTrace_186188 : CollatzResearch.WordTrace tailWord_186188 prefixEnd_186188 84981276532820242038883 := by
  unfold tailWord_186188
  simp only [CollatzResearch.WordTrace]
  refine ⟨3395417124740074611955609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4527222832986766149274145 3395417124740074611955609)
  ·
    refine ⟨2546562843555055958966707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3395417124740074611955609 2546562843555055958966707)
    ·
      refine ⟨3819844265332583938450061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2546562843555055958966707 3819844265332583938450061)
      ·
        refine ⟨1432441599499718976918773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3819844265332583938450061 1432441599499718976918773)
        ·
          refine ⟨134291399953098654086135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1432441599499718976918773 134291399953098654086135)
          ·
            refine ⟨201437099929647981129203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134291399953098654086135 201437099929647981129203)
            ·
              refine ⟨302155649894471971693805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201437099929647981129203 302155649894471971693805)
              ·
                refine ⟨113308368710426989385177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302155649894471971693805 113308368710426989385177)
                ·
                  refine ⟨84981276532820242038883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113308368710426989385177 84981276532820242038883)
                  ·
                    rfl

theorem cell20_186188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_186188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186188 prefixEnd_186188 := by exact prefixLift 186188
  have htrace : WordTrace (prefixWord ++ tailWord_186188) baseStart_186188 baseEnd_186188 := by
    simpa [prefixWord, tailWord_186188, baseEnd_186188] using wordTrace_append hprefix tailTrace_186188
  have hstable : (prefixWord ++ tailWord_186188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186188).length < 2 ^ (prefixWord ++ tailWord_186188).sum := by decide
  have hdescent : baseEnd_186188 < baseStart_186188 := by decide
  rcases family_descends (prefixWord ++ tailWord_186188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186199 : List Nat := [1, 1, 3, 2, 6, 1, 6]
def baseStart_186199 : Nat := 118140960795 + 186199 * 2 ^ 59
def prefixEnd_186199 : Nat := 4983230072969 + 3 ^ 40 * 186199 * 2
def baseEnd_186199 : Nat := 9442921914728121408019

theorem tailTrace_186199 : CollatzResearch.WordTrace tailWord_186199 prefixEnd_186199 9442921914728121408019 := by
  unfold tailWord_186199
  simp only [CollatzResearch.WordTrace]
  refine ⟨6791235452440298102561651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4527490301626865401707767 6791235452440298102561651)
  ·
    refine ⟨10186853178660447153842477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6791235452440298102561651 10186853178660447153842477)
    ·
      refine ⟨3820069941997667682690929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10186853178660447153842477 3820069941997667682690929)
      ·
        refine ⟨2865052456498250762018197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3820069941997667682690929 2865052456498250762018197)
        ·
          refine ⟨134299333898355504469603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2865052456498250762018197 134299333898355504469603)
          ·
            refine ⟨201449000847533256704405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134299333898355504469603 201449000847533256704405)
            ·
              refine ⟨9442921914728121408019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 201449000847533256704405 9442921914728121408019)
              ·
                rfl

theorem cell20_186199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 6].length) (baseStart_186199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186199 prefixEnd_186199 := by exact prefixLift 186199
  have htrace : WordTrace (prefixWord ++ tailWord_186199) baseStart_186199 baseEnd_186199 := by
    simpa [prefixWord, tailWord_186199, baseEnd_186199] using wordTrace_append hprefix tailTrace_186199
  have hstable : (prefixWord ++ tailWord_186199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186199).length < 2 ^ (prefixWord ++ tailWord_186199).sum := by decide
  have hdescent : baseEnd_186199 < baseStart_186199 := by decide
  rcases family_descends (prefixWord ++ tailWord_186199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186220 : List Nat := [2, 2, 1, 1, 4, 3, 2, 5]
def baseStart_186220 : Nat := 118140960795 + 186220 * 2 ^ 59
def prefixEnd_186220 : Nat := 4983230072969 + 3 ^ 40 * 186220 * 2
def baseEnd_186220 : Nat := 28331960734923450990695

theorem tailTrace_186220 : CollatzResearch.WordTrace tailWord_186220 prefixEnd_186220 28331960734923450990695 := by
  unfold tailWord_186220
  simp only [CollatzResearch.WordTrace]
  refine ⟨3396000692682109344538057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4528000923576145792717409 3396000692682109344538057)
  ·
    refine ⟨2547000519511582008403543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3396000692682109344538057 2547000519511582008403543)
    ·
      refine ⟨3820500779267373012605315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2547000519511582008403543 3820500779267373012605315)
      ·
        refine ⟨5730751168901059518907973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3820500779267373012605315 5730751168901059518907973)
        ·
          refine ⟨1074515844168948659795245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5730751168901059518907973 1074515844168948659795245)
          ·
            refine ⟨402943441563355747423217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1074515844168948659795245 402943441563355747423217)
            ·
              refine ⟨302207581172516810567413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402943441563355747423217 302207581172516810567413)
              ·
                refine ⟨28331960734923450990695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302207581172516810567413 28331960734923450990695)
                ·
                  rfl

theorem cell20_186220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_186220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186220 prefixEnd_186220 := by exact prefixLift 186220
  have htrace : WordTrace (prefixWord ++ tailWord_186220) baseStart_186220 baseEnd_186220 := by
    simpa [prefixWord, tailWord_186220, baseEnd_186220] using wordTrace_append hprefix tailTrace_186220
  have hstable : (prefixWord ++ tailWord_186220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186220).length < 2 ^ (prefixWord ++ tailWord_186220).sum := by decide
  have hdescent : baseEnd_186220 < baseStart_186220 := by decide
  rcases family_descends (prefixWord ++ tailWord_186220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186234 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_186234 : Nat := 118140960795 + 186234 * 2 ^ 59
def prefixEnd_186234 : Nat := 4983230072969 + 3 ^ 40 * 186234 * 2
def baseEnd_186234 : Nat := 85002272186248526505361

theorem tailTrace_186234 : CollatzResearch.WordTrace tailWord_186234 prefixEnd_186234 85002272186248526505361 := by
  unfold tailWord_186234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698128001828374770021439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4528341338208999386723837 1698128001828374770021439)
  ·
    refine ⟨2547192002742562155032159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1698128001828374770021439 2547192002742562155032159)
    ·
      refine ⟨3820788004113843232548239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2547192002742562155032159 3820788004113843232548239)
      ·
        refine ⟨5731182006170764848822359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3820788004113843232548239 5731182006170764848822359)
        ·
          refine ⟨8596773009256147273233539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5731182006170764848822359 8596773009256147273233539)
          ·
            refine ⟨12895159513884220909850309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8596773009256147273233539 12895159513884220909850309)
            ·
              refine ⟨2417842408853291420596933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12895159513884220909850309 2417842408853291420596933)
              ·
                refine ⟨453345451659992141361925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2417842408853291420596933 453345451659992141361925)
                ·
                  refine ⟨85002272186248526505361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453345451659992141361925 85002272186248526505361)
                  ·
                    rfl

theorem cell20_186234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_186234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186234 prefixEnd_186234 := by exact prefixLift 186234
  have htrace : WordTrace (prefixWord ++ tailWord_186234) baseStart_186234 baseEnd_186234 := by
    simpa [prefixWord, tailWord_186234, baseEnd_186234] using wordTrace_append hprefix tailTrace_186234
  have hstable : (prefixWord ++ tailWord_186234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186234).length < 2 ^ (prefixWord ++ tailWord_186234).sum := by decide
  have hdescent : baseEnd_186234 < baseStart_186234 := by decide
  rcases family_descends (prefixWord ++ tailWord_186234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186251 : List Nat := [1, 1, 1, 1, 4, 2, 1, 7, 2]
def baseStart_186251 : Nat := 118140960795 + 186251 * 2 ^ 59
def prefixEnd_186251 : Nat := 4983230072969 + 3 ^ 40 * 186251 * 2
def baseEnd_186251 : Nat := 85010031449472022938625

theorem tailTrace_186251 : CollatzResearch.WordTrace tailWord_186251 prefixEnd_186251 85010031449472022938625 := by
  unfold tailWord_186251
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793132048251910983454607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4528754698834607322303071 6793132048251910983454607)
  ·
    refine ⟨10189698072377866475181911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6793132048251910983454607 10189698072377866475181911)
    ·
      refine ⟨15284547108566799712772867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10189698072377866475181911 15284547108566799712772867)
      ·
        refine ⟨22926820662850199569159301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15284547108566799712772867 22926820662850199569159301)
        ·
          refine ⟨4298778874284412419217369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22926820662850199569159301 4298778874284412419217369)
          ·
            refine ⟨3224084155713309314413027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4298778874284412419217369 3224084155713309314413027)
            ·
              refine ⟨4836126233569963971619541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224084155713309314413027 4836126233569963971619541)
              ·
                refine ⟨113346708599296030584833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4836126233569963971619541 113346708599296030584833)
                ·
                  refine ⟨85010031449472022938625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113346708599296030584833 85010031449472022938625)
                  ·
                    rfl

theorem cell20_186251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 2].length) (baseStart_186251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186251 prefixEnd_186251 := by exact prefixLift 186251
  have htrace : WordTrace (prefixWord ++ tailWord_186251) baseStart_186251 baseEnd_186251 := by
    simpa [prefixWord, tailWord_186251, baseEnd_186251] using wordTrace_append hprefix tailTrace_186251
  have hstable : (prefixWord ++ tailWord_186251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186251).length < 2 ^ (prefixWord ++ tailWord_186251).sum := by decide
  have hdescent : baseEnd_186251 < baseStart_186251 := by decide
  rcases family_descends (prefixWord ++ tailWord_186251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186258 : List Nat := [3, 2, 3, 2, 1, 9]
def baseStart_186258 : Nat := 118140960795 + 186258 * 2 ^ 59
def prefixEnd_186258 : Nat := 4983230072969 + 3 ^ 40 * 186258 * 2
def baseEnd_186258 : Nat := 3148638016304115174269

theorem tailTrace_186258 : CollatzResearch.WordTrace tailWord_186258 prefixEnd_186258 3148638016304115174269 := by
  unfold tailWord_186258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698346839806637794739857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4528924906151034119306285 1698346839806637794739857)
  ·
    refine ⟨1273760129854978346054893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1698346839806637794739857 1273760129854978346054893)
    ·
      refine ⟨477660048695616879770585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1273760129854978346054893 477660048695616879770585)
      ·
        refine ⟨358245036521712659827939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477660048695616879770585 358245036521712659827939)
        ·
          refine ⟨537367554782568989741909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358245036521712659827939 537367554782568989741909)
          ·
            refine ⟨3148638016304115174269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 537367554782568989741909 3148638016304115174269)
            ·
              rfl

theorem cell20_186258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 9].length) (baseStart_186258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186258 prefixEnd_186258 := by exact prefixLift 186258
  have htrace : WordTrace (prefixWord ++ tailWord_186258) baseStart_186258 baseEnd_186258 := by
    simpa [prefixWord, tailWord_186258, baseEnd_186258] using wordTrace_append hprefix tailTrace_186258
  have hstable : (prefixWord ++ tailWord_186258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186258).length < 2 ^ (prefixWord ++ tailWord_186258).sum := by decide
  have hdescent : baseEnd_186258 < baseStart_186258 := by decide
  rcases family_descends (prefixWord ++ tailWord_186258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186265 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 3]
def baseStart_186265 : Nat := 118140960795 + 186265 * 2 ^ 59
def prefixEnd_186265 : Nat := 4983230072969 + 3 ^ 40 * 186265 * 2
def baseEnd_186265 : Nat := 85016421430950196471901

theorem tailTrace_186265 : CollatzResearch.WordTrace tailWord_186265 prefixEnd_186265 85016421430950196471901 := by
  unfold tailWord_186265
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793642670201191374464249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4529095113467460916309499 6793642670201191374464249)
  ·
    refine ⟨5095232002650893530848187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6793642670201191374464249 5095232002650893530848187)
    ·
      refine ⟨7642848003976340296272281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5095232002650893530848187 7642848003976340296272281)
      ·
        refine ⟨5732136002982255222204211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7642848003976340296272281 5732136002982255222204211)
        ·
          refine ⟨8598204004473382833306317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5732136002982255222204211 8598204004473382833306317)
          ·
            refine ⟨3224326501677518562489869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8598204004473382833306317 3224326501677518562489869)
            ·
              refine ⟨1209122438129069460933701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3224326501677518562489869 1209122438129069460933701)
              ·
                refine ⟨226710457149200523925069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1209122438129069460933701 226710457149200523925069)
                ·
                  refine ⟨85016421430950196471901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226710457149200523925069 85016421430950196471901)
                  ·
                    rfl

theorem cell20_186265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_186265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186265 prefixEnd_186265 := by exact prefixLift 186265
  have htrace : WordTrace (prefixWord ++ tailWord_186265) baseStart_186265 baseEnd_186265 := by
    simpa [prefixWord, tailWord_186265, baseEnd_186265] using wordTrace_append hprefix tailTrace_186265
  have hstable : (prefixWord ++ tailWord_186265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186265).length < 2 ^ (prefixWord ++ tailWord_186265).sum := by decide
  have hdescent : baseEnd_186265 < baseStart_186265 := by decide
  rcases family_descends (prefixWord ++ tailWord_186265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186272 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_186272 : Nat := 118140960795 + 186272 * 2 ^ 59
def prefixEnd_186272 : Nat := 4983230072969 + 3 ^ 40 * 186272 * 2
def baseEnd_186272 : Nat := 85019616421689283238539

theorem tailTrace_186272 : CollatzResearch.WordTrace tailWord_186272 prefixEnd_186272 85019616421689283238539 := by
  unfold tailWord_186272
  simp only [CollatzResearch.WordTrace]
  refine ⟨3396948990587915784984535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4529265320783887713312713 3396948990587915784984535)
  ·
    refine ⟨5095423485881873677476803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3396948990587915784984535 5095423485881873677476803)
    ·
      refine ⟨7643135228822810516215205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5095423485881873677476803 7643135228822810516215205)
      ·
        refine ⟨1433087855404276971790351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7643135228822810516215205 1433087855404276971790351)
        ·
          refine ⟨2149631783106415457685527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433087855404276971790351 2149631783106415457685527)
          ·
            refine ⟨3224447674659623186528291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149631783106415457685527 3224447674659623186528291)
            ·
              refine ⟨4836671511989434779792437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224447674659623186528291 4836671511989434779792437)
              ·
                refine ⟨453437954249009510605541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4836671511989434779792437 453437954249009510605541)
                ·
                  refine ⟨85019616421689283238539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453437954249009510605541 85019616421689283238539)
                  ·
                    rfl

theorem cell20_186272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_186272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186272 prefixEnd_186272 := by exact prefixLift 186272
  have htrace : WordTrace (prefixWord ++ tailWord_186272) baseStart_186272 baseEnd_186272 := by
    simpa [prefixWord, tailWord_186272, baseEnd_186272] using wordTrace_append hprefix tailTrace_186272
  have hstable : (prefixWord ++ tailWord_186272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186272).length < 2 ^ (prefixWord ++ tailWord_186272).sum := by decide
  have hdescent : baseEnd_186272 < baseStart_186272 := by decide
  rcases family_descends (prefixWord ++ tailWord_186272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186289 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 4]
def baseStart_186289 : Nat := 118140960795 + 186289 * 2 ^ 59
def prefixEnd_186289 : Nat := 4983230072969 + 3 ^ 40 * 186289 * 2
def baseEnd_186289 : Nat := 85027375684912779671803

theorem tailTrace_186289 : CollatzResearch.WordTrace tailWord_186289 prefixEnd_186289 85027375684912779671803 := by
  unfold tailWord_186289
  simp only [CollatzResearch.WordTrace]
  refine ⟨6794518022114243473337921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4529678681409495648891947 6794518022114243473337921)
  ·
    refine ⟨5095888516585682605003441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6794518022114243473337921 5095888516585682605003441)
    ·
      refine ⟨3821916387439261953752581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5095888516585682605003441 3821916387439261953752581)
      ·
        refine ⟨716609322644861616328609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3821916387439261953752581 716609322644861616328609)
        ·
          refine ⟨537456991983646212246457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716609322644861616328609 537456991983646212246457)
          ·
            refine ⟨403092743987734659184843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537456991983646212246457 403092743987734659184843)
            ·
              refine ⟨604639115981601988777265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403092743987734659184843 604639115981601988777265)
              ·
                refine ⟨453479336986201491582949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604639115981601988777265 453479336986201491582949)
                ·
                  refine ⟨85027375684912779671803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453479336986201491582949 85027375684912779671803)
                  ·
                    rfl

theorem cell20_186289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_186289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186289 prefixEnd_186289 := by exact prefixLift 186289
  have htrace : WordTrace (prefixWord ++ tailWord_186289) baseStart_186289 baseEnd_186289 := by
    simpa [prefixWord, tailWord_186289, baseEnd_186289] using wordTrace_append hprefix tailTrace_186289
  have hstable : (prefixWord ++ tailWord_186289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186289).length < 2 ^ (prefixWord ++ tailWord_186289).sum := by decide
  have hdescent : baseEnd_186289 < baseStart_186289 := by decide
  rcases family_descends (prefixWord ++ tailWord_186289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186296 : List Nat := [2, 1, 2, 1, 2, 3, 5, 4]
def baseStart_186296 : Nat := 118140960795 + 186296 * 2 ^ 59
def prefixEnd_186296 : Nat := 4983230072969 + 3 ^ 40 * 186296 * 2
def baseEnd_186296 : Nat := 28343523558550622146147

theorem tailTrace_186296 : CollatzResearch.WordTrace tailWord_186296 prefixEnd_186296 28343523558550622146147 := by
  unfold tailWord_186296
  simp only [CollatzResearch.WordTrace]
  refine ⟨3397386666544441834421371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4529848888725922445895161 3397386666544441834421371)
  ·
    refine ⟨5096079999816662751632057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3397386666544441834421371 5096079999816662751632057)
    ·
      refine ⟨3822059999862497063724043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5096079999816662751632057 3822059999862497063724043)
      ·
        refine ⟨5733089999793745595586065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3822059999862497063724043 5733089999793745595586065)
        ·
          refine ⟨4299817499845309196689549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5733089999793745595586065 4299817499845309196689549)
          ·
            refine ⟨1612431562441990948758581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4299817499845309196689549 1612431562441990948758581)
            ·
              refine ⟨151165458978936651446117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1612431562441990948758581 151165458978936651446117)
              ·
                refine ⟨28343523558550622146147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151165458978936651446117 28343523558550622146147)
                ·
                  rfl

theorem cell20_186296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_186296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186296 prefixEnd_186296 := by exact prefixLift 186296
  have htrace : WordTrace (prefixWord ++ tailWord_186296) baseStart_186296 baseEnd_186296 := by
    simpa [prefixWord, tailWord_186296, baseEnd_186296] using wordTrace_append hprefix tailTrace_186296
  have hstable : (prefixWord ++ tailWord_186296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186296).length < 2 ^ (prefixWord ++ tailWord_186296).sum := by decide
  have hdescent : baseEnd_186296 < baseStart_186296 := by decide
  rcases family_descends (prefixWord ++ tailWord_186296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186327 : List Nat := [1, 1, 3, 2, 1, 1, 3, 6, 2]
def baseStart_186327 : Nat := 118140960795 + 186327 * 2 ^ 59
def prefixEnd_186327 : Nat := 4983230072969 + 3 ^ 40 * 186327 * 2
def baseEnd_186327 : Nat := 85044719920353536404981

theorem tailTrace_186327 : CollatzResearch.WordTrace tailWord_186327 prefixEnd_186327 85044719920353536404981 := by
  unfold tailWord_186327
  simp only [CollatzResearch.WordTrace]
  refine ⟨6795903995976575963221235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4530602663984383975480823 6795903995976575963221235)
  ·
    refine ⟨10193855993964863944831853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6795903995976575963221235 10193855993964863944831853)
    ·
      refine ⟨3822695997736823979311945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10193855993964863944831853 3822695997736823979311945)
      ·
        refine ⟨2867021998302617984483959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3822695997736823979311945 2867021998302617984483959)
        ·
          refine ⟨4300532997453926976725939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2867021998302617984483959 4300532997453926976725939)
          ·
            refine ⟨6450799496180890465088909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300532997453926976725939 6450799496180890465088909)
            ·
              refine ⟨2419049811067833924408341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6450799496180890465088909 2419049811067833924408341)
              ·
                refine ⟨113392959893804715206641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2419049811067833924408341 113392959893804715206641)
                ·
                  refine ⟨85044719920353536404981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113392959893804715206641 85044719920353536404981)
                  ·
                    rfl

theorem cell20_186327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 2].length) (baseStart_186327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186327 prefixEnd_186327 := by exact prefixLift 186327
  have htrace : WordTrace (prefixWord ++ tailWord_186327) baseStart_186327 baseEnd_186327 := by
    simpa [prefixWord, tailWord_186327, baseEnd_186327] using wordTrace_append hprefix tailTrace_186327
  have hstable : (prefixWord ++ tailWord_186327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186327).length < 2 ^ (prefixWord ++ tailWord_186327).sum := by decide
  have hdescent : baseEnd_186327 < baseStart_186327 := by decide
  rcases family_descends (prefixWord ++ tailWord_186327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186374 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_186374 : Nat := 118140960795 + 186374 * 2 ^ 59
def prefixEnd_186374 : Nat := 4983230072969 + 3 ^ 40 * 186374 * 2
def baseEnd_186374 : Nat := 85066172001030261838123

theorem tailTrace_186374 : CollatzResearch.WordTrace tailWord_186374 prefixEnd_186374 85066172001030261838123 := by
  unfold tailWord_186374
  simp only [CollatzResearch.WordTrace]
  refine ⟨212425569587696968443193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4531745484537535326788117 212425569587696968443193)
  ·
    refine ⟨159319177190772726332395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212425569587696968443193 159319177190772726332395)
    ·
      refine ⟨238978765786159089498593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159319177190772726332395 238978765786159089498593)
      ·
        refine ⟨179234074339619317123945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238978765786159089498593 179234074339619317123945)
        ·
          refine ⟨134425555754714487842959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179234074339619317123945 134425555754714487842959)
          ·
            refine ⟨201638333632071731764439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134425555754714487842959 201638333632071731764439)
            ·
              refine ⟨302457500448107597646659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201638333632071731764439 302457500448107597646659)
              ·
                refine ⟨453686250672161396469989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302457500448107597646659 453686250672161396469989)
                ·
                  refine ⟨85066172001030261838123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453686250672161396469989 85066172001030261838123)
                  ·
                    rfl

theorem cell20_186374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_186374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186374 prefixEnd_186374 := by exact prefixLift 186374
  have htrace : WordTrace (prefixWord ++ tailWord_186374) baseStart_186374 baseEnd_186374 := by
    simpa [prefixWord, tailWord_186374, baseEnd_186374] using wordTrace_append hprefix tailTrace_186374
  have hstable : (prefixWord ++ tailWord_186374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186374).length < 2 ^ (prefixWord ++ tailWord_186374).sum := by decide
  have hdescent : baseEnd_186374 < baseStart_186374 := by decide
  rcases family_descends (prefixWord ++ tailWord_186374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186379 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 3]
def baseStart_186379 : Nat := 118140960795 + 186379 * 2 ^ 59
def prefixEnd_186379 : Nat := 4983230072969 + 3 ^ 40 * 186379 * 2
def baseEnd_186379 : Nat := 85068454137272466671435

theorem tailTrace_186379 : CollatzResearch.WordTrace tailWord_186379 prefixEnd_186379 85068454137272466671435 := by
  unfold tailWord_186379
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797800591788188844114191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4531867061192125896076127 6797800591788188844114191)
  ·
    refine ⟨10196700887682283266171287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6797800591788188844114191 10196700887682283266171287)
    ·
      refine ⟨15295051331523424899256931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10196700887682283266171287 15295051331523424899256931)
      ·
        refine ⟨22942576997285137348885397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15295051331523424899256931 22942576997285137348885397)
        ·
          refine ⟨1075433296747740813229003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22942576997285137348885397 1075433296747740813229003)
          ·
            refine ⟨1613149945121611219843505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075433296747740813229003 1613149945121611219843505)
            ·
              refine ⟨1209862458841208414882629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613149945121611219843505 1209862458841208414882629)
              ·
                refine ⟨226849211032726577790493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1209862458841208414882629 226849211032726577790493)
                ·
                  refine ⟨85068454137272466671435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226849211032726577790493 85068454137272466671435)
                  ·
                    rfl

theorem cell20_186379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 3].length) (baseStart_186379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186379 prefixEnd_186379 := by exact prefixLift 186379
  have htrace : WordTrace (prefixWord ++ tailWord_186379) baseStart_186379 baseEnd_186379 := by
    simpa [prefixWord, tailWord_186379, baseEnd_186379] using wordTrace_append hprefix tailTrace_186379
  have hstable : (prefixWord ++ tailWord_186379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186379).length < 2 ^ (prefixWord ++ tailWord_186379).sum := by decide
  have hdescent : baseEnd_186379 < baseStart_186379 := by decide
  rcases family_descends (prefixWord ++ tailWord_186379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186388 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 3]
def baseStart_186388 : Nat := 118140960795 + 186388 * 2 ^ 59
def prefixEnd_186388 : Nat := 4983230072969 + 3 ^ 40 * 186388 * 2
def baseEnd_186388 : Nat := 85072561982508435371399

theorem tailTrace_186388 : CollatzResearch.WordTrace tailWord_186388 prefixEnd_186388 85072561982508435371399 := by
  unfold tailWord_186388
  simp only [CollatzResearch.WordTrace]
  refine ⟨3399064424377791690595909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4532085899170388920794545 3399064424377791690595909)
  ·
    refine ⟨637324579570835941986733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3399064424377791690595909 637324579570835941986733)
    ·
      refine ⟨238996717339063478245025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 637324579570835941986733 238996717339063478245025)
      ·
        refine ⟨179247538004297608683769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238996717339063478245025 179247538004297608683769)
        ·
          refine ⟨134435653503223206512827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179247538004297608683769 134435653503223206512827)
          ·
            refine ⟨201653480254834809769241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134435653503223206512827 201653480254834809769241)
            ·
              refine ⟨151240110191126107326931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201653480254834809769241 151240110191126107326931)
              ·
                refine ⟨226860165286689160990397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151240110191126107326931 226860165286689160990397)
                ·
                  refine ⟨85072561982508435371399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226860165286689160990397 85072561982508435371399)
                  ·
                    rfl

theorem cell20_186388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_186388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186388 prefixEnd_186388 := by exact prefixLift 186388
  have htrace : WordTrace (prefixWord ++ tailWord_186388) baseStart_186388 baseEnd_186388 := by
    simpa [prefixWord, tailWord_186388, baseEnd_186388] using wordTrace_append hprefix tailTrace_186388
  have hstable : (prefixWord ++ tailWord_186388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186388).length < 2 ^ (prefixWord ++ tailWord_186388).sum := by decide
  have hdescent : baseEnd_186388 < baseStart_186388 := by decide
  rcases family_descends (prefixWord ++ tailWord_186388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186396 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 3]
def baseStart_186396 : Nat := 118140960795 + 186396 * 2 ^ 59
def prefixEnd_186396 : Nat := 4983230072969 + 3 ^ 40 * 186396 * 2
def baseEnd_186396 : Nat := 85076213400495963104699

theorem tailTrace_186396 : CollatzResearch.WordTrace tailWord_186396 prefixEnd_186396 85076213400495963104699 := by
  unfold tailWord_186396
  simp only [CollatzResearch.WordTrace]
  refine ⟨3399210316363300373741521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4532280421817733831655361 3399210316363300373741521)
  ·
    refine ⟨2549407737272475280306141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3399210316363300373741521 2549407737272475280306141)
    ·
      refine ⟨956027901477178230114803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2549407737272475280306141 956027901477178230114803)
      ·
        refine ⟨1434041852215767345172205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956027901477178230114803 1434041852215767345172205)
        ·
          refine ⟨537765694580912754439577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1434041852215767345172205 537765694580912754439577)
          ·
            refine ⟨403324270935684565829683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537765694580912754439577 403324270935684565829683)
            ·
              refine ⟨604986406403526848744525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403324270935684565829683 604986406403526848744525)
              ·
                refine ⟨226869902401322568279197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 604986406403526848744525 226869902401322568279197)
                ·
                  refine ⟨85076213400495963104699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226869902401322568279197 85076213400495963104699)
                  ·
                    rfl

theorem cell20_186396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_186396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186396 prefixEnd_186396 := by exact prefixLift 186396
  have htrace : WordTrace (prefixWord ++ tailWord_186396) baseStart_186396 baseEnd_186396 := by
    simpa [prefixWord, tailWord_186396, baseEnd_186396] using wordTrace_append hprefix tailTrace_186396
  have hstable : (prefixWord ++ tailWord_186396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186396).length < 2 ^ (prefixWord ++ tailWord_186396).sum := by decide
  have hdescent : baseEnd_186396 < baseStart_186396 := by decide
  rcases family_descends (prefixWord ++ tailWord_186396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186410 : List Nat := [3, 1, 4, 1, 2, 1, 2, 6]
def baseStart_186410 : Nat := 118140960795 + 186410 * 2 ^ 59
def prefixEnd_186410 : Nat := 4983230072969 + 3 ^ 40 * 186410 * 2
def baseEnd_186410 : Nat := 28360867793991378879325

theorem tailTrace_186410 : CollatzResearch.WordTrace tailWord_186410 prefixEnd_186410 28360867793991378879325 := by
  unfold tailWord_186410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1699732813668970284623171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4532620836450587425661789 1699732813668970284623171)
  ·
    refine ⟨2549599220503455426934757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1699732813668970284623171 2549599220503455426934757)
    ·
      refine ⟨478049853844397892550267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2549599220503455426934757 478049853844397892550267)
      ·
        refine ⟨717074780766596838825401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478049853844397892550267 717074780766596838825401)
        ·
          refine ⟨537806085574947629119051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717074780766596838825401 537806085574947629119051)
          ·
            refine ⟨806709128362421443678577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537806085574947629119051 806709128362421443678577)
            ·
              refine ⟨605031846271816082758933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806709128362421443678577 605031846271816082758933)
              ·
                refine ⟨28360867793991378879325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 605031846271816082758933 28360867793991378879325)
                ·
                  rfl

theorem cell20_186410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_186410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186410 prefixEnd_186410 := by exact prefixLift 186410
  have htrace : WordTrace (prefixWord ++ tailWord_186410) baseStart_186410 baseEnd_186410 := by
    simpa [prefixWord, tailWord_186410, baseEnd_186410] using wordTrace_append hprefix tailTrace_186410
  have hstable : (prefixWord ++ tailWord_186410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186410).length < 2 ^ (prefixWord ++ tailWord_186410).sum := by decide
  have hdescent : baseEnd_186410 < baseStart_186410 := by decide
  rcases family_descends (prefixWord ++ tailWord_186410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186441 : List Nat := [1, 2, 1, 1, 2, 2, 5, 4, 2]
def baseStart_186441 : Nat := 118140960795 + 186441 * 2 ^ 59
def prefixEnd_186441 : Nat := 4983230072969 + 3 ^ 40 * 186441 * 2
def baseEnd_186441 : Nat := 85096752626675806604515

theorem tailTrace_186441 : CollatzResearch.WordTrace tailWord_186441 prefixEnd_186441 85096752626675806604515 := by
  unfold tailWord_186441
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800061917563573432871177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4533374611709048955247451 6800061917563573432871177)
  ·
    refine ⟨5100046438172680074653383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6800061917563573432871177 5100046438172680074653383)
    ·
      refine ⟨7650069657259020111980075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5100046438172680074653383 7650069657259020111980075)
      ·
        refine ⟨11475104485888530167970113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7650069657259020111980075 11475104485888530167970113)
        ·
          refine ⟨8606328364416397625977585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11475104485888530167970113 8606328364416397625977585)
          ·
            refine ⟨6454746273312298219483189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8606328364416397625977585 6454746273312298219483189)
            ·
              refine ⟨605132463123027958076549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6454746273312298219483189 605132463123027958076549)
              ·
                refine ⟨113462336835567742139353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 605132463123027958076549 113462336835567742139353)
                ·
                  refine ⟨85096752626675806604515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113462336835567742139353 85096752626675806604515)
                  ·
                    rfl

theorem cell20_186441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 2].length) (baseStart_186441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186441 prefixEnd_186441 := by exact prefixLift 186441
  have htrace : WordTrace (prefixWord ++ tailWord_186441) baseStart_186441 baseEnd_186441 := by
    simpa [prefixWord, tailWord_186441, baseEnd_186441] using wordTrace_append hprefix tailTrace_186441
  have hstable : (prefixWord ++ tailWord_186441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186441).length < 2 ^ (prefixWord ++ tailWord_186441).sum := by decide
  have hdescent : baseEnd_186441 < baseStart_186441 := by decide
  rcases family_descends (prefixWord ++ tailWord_186441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186455 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 3]
def baseStart_186455 : Nat := 118140960795 + 186455 * 2 ^ 59
def prefixEnd_186455 : Nat := 4983230072969 + 3 ^ 40 * 186455 * 2
def baseEnd_186455 : Nat := 85103142608153980137791

theorem tailTrace_186455 : CollatzResearch.WordTrace tailWord_186455 prefixEnd_186455 85103142608153980137791 := by
  unfold tailWord_186455
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800572539512853823880819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4533715026341902549253879 6800572539512853823880819)
  ·
    refine ⟨10200858809269280735821229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6800572539512853823880819 10200858809269280735821229)
    ·
      refine ⟨3825322053475980275932961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10200858809269280735821229 3825322053475980275932961)
      ·
        refine ⟨2868991540106985206949721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3825322053475980275932961 2868991540106985206949721)
        ·
          refine ⟨2151743655080238905212291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2868991540106985206949721 2151743655080238905212291)
          ·
            refine ⟨3227615482620358357818437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151743655080238905212291 3227615482620358357818437)
            ·
              refine ⟨605177902991317192090957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3227615482620358357818437 605177902991317192090957)
              ·
                refine ⟨226941713621743947034109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 605177902991317192090957 226941713621743947034109)
                ·
                  refine ⟨85103142608153980137791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226941713621743947034109 85103142608153980137791)
                  ·
                    rfl

theorem cell20_186455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 3].length) (baseStart_186455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186455 prefixEnd_186455 := by exact prefixLift 186455
  have htrace : WordTrace (prefixWord ++ tailWord_186455) baseStart_186455 baseEnd_186455 := by
    simpa [prefixWord, tailWord_186455, baseEnd_186455] using wordTrace_append hprefix tailTrace_186455
  have hstable : (prefixWord ++ tailWord_186455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186455).length < 2 ^ (prefixWord ++ tailWord_186455).sum := by decide
  have hdescent : baseEnd_186455 < baseStart_186455 := by decide
  rcases family_descends (prefixWord ++ tailWord_186455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186479 : List Nat := [1, 1, 2, 1, 3, 4, 1, 5, 2]
def baseStart_186479 : Nat := 118140960795 + 186479 * 2 ^ 59
def prefixEnd_186479 : Nat := 4983230072969 + 3 ^ 40 * 186479 * 2
def baseEnd_186479 : Nat := 85114096862116563337693

theorem tailTrace_186479 : CollatzResearch.WordTrace tailWord_186479 prefixEnd_186479 85114096862116563337693 := by
  unfold tailWord_186479
  simp only [CollatzResearch.WordTrace]
  refine ⟨6801447891425905922754491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4534298594283937281836327 6801447891425905922754491)
  ·
    refine ⟨10202171837138858884131737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6801447891425905922754491 10202171837138858884131737)
    ·
      refine ⟨7651628877854144163098803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10202171837138858884131737 7651628877854144163098803)
      ·
        refine ⟨11477443316781216244648205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7651628877854144163098803 11477443316781216244648205)
        ·
          refine ⟨4304041243792956091743077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11477443316781216244648205 4304041243792956091743077)
          ·
            refine ⟨807007733211179267201827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4304041243792956091743077 807007733211179267201827)
            ·
              refine ⟨1210511599816768900802741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807007733211179267201827 1210511599816768900802741)
              ·
                refine ⟨113485462482822084450257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1210511599816768900802741 113485462482822084450257)
                ·
                  refine ⟨85114096862116563337693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113485462482822084450257 85114096862116563337693)
                  ·
                    rfl

theorem cell20_186479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 2].length) (baseStart_186479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186479 prefixEnd_186479 := by exact prefixLift 186479
  have htrace : WordTrace (prefixWord ++ tailWord_186479) baseStart_186479 baseEnd_186479 := by
    simpa [prefixWord, tailWord_186479, baseEnd_186479] using wordTrace_append hprefix tailTrace_186479
  have hstable : (prefixWord ++ tailWord_186479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186479).length < 2 ^ (prefixWord ++ tailWord_186479).sum := by decide
  have hdescent : baseEnd_186479 < baseStart_186479 := by decide
  rcases family_descends (prefixWord ++ tailWord_186479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186486 : List Nat := [5, 1, 1, 2, 1, 3, 7]
def baseStart_186486 : Nat := 118140960795 + 186486 * 2 ^ 59
def prefixEnd_186486 : Nat := 4983230072969 + 3 ^ 40 * 186486 * 2
def baseEnd_186486 : Nat := 9457476872539516678259

theorem tailTrace_186486 : CollatzResearch.WordTrace tailWord_186486 prefixEnd_186486 9457476872539516678259 := by
  unfold tailWord_186486
  simp only [CollatzResearch.WordTrace]
  refine ⟨425106450150034132391207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4534468801600364078839541 425106450150034132391207)
  ·
    refine ⟨637659675225051198586811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 425106450150034132391207 637659675225051198586811)
    ·
      refine ⟨956489512837576797880217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 637659675225051198586811 956489512837576797880217)
      ·
        refine ⟨717367134628182598410163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 956489512837576797880217 717367134628182598410163)
        ·
          refine ⟨1076050701942273897615245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717367134628182598410163 1076050701942273897615245)
          ·
            refine ⟨403519013228352711605717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1076050701942273897615245 403519013228352711605717)
            ·
              refine ⟨9457476872539516678259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 403519013228352711605717 9457476872539516678259)
              ·
                rfl

theorem cell20_186486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 7].length) (baseStart_186486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186486 prefixEnd_186486 := by exact prefixLift 186486
  have htrace : WordTrace (prefixWord ++ tailWord_186486) baseStart_186486 baseEnd_186486 := by
    simpa [prefixWord, tailWord_186486, baseEnd_186486] using wordTrace_append hprefix tailTrace_186486
  have hstable : (prefixWord ++ tailWord_186486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186486).length < 2 ^ (prefixWord ++ tailWord_186486).sum := by decide
  have hdescent : baseEnd_186486 < baseStart_186486 := by decide
  rcases family_descends (prefixWord ++ tailWord_186486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186493 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 5]
def baseStart_186493 : Nat := 118140960795 + 186493 * 2 ^ 59
def prefixEnd_186493 : Nat := 4983230072969 + 3 ^ 40 * 186493 * 2
def baseEnd_186493 : Nat := 85120486843594736870969

theorem tailTrace_186493 : CollatzResearch.WordTrace tailWord_186493 prefixEnd_186493 85120486843594736870969 := by
  unfold tailWord_186493
  simp only [CollatzResearch.WordTrace]
  refine ⟨6801958513375186313764133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4534639008916790875842755 6801958513375186313764133)
  ·
    refine ⟨1275367221257847433830775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6801958513375186313764133 1275367221257847433830775)
    ·
      refine ⟨1913050831886771150746163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275367221257847433830775 1913050831886771150746163)
      ·
        refine ⟨2869576247830156726119245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913050831886771150746163 2869576247830156726119245)
        ·
          refine ⟨1076091092936308772294717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2869576247830156726119245 1076091092936308772294717)
          ·
            refine ⟨403534159851115789610519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1076091092936308772294717 403534159851115789610519)
            ·
              refine ⟨605301239776673684415779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403534159851115789610519 605301239776673684415779)
              ·
                refine ⟨907951859665010526623669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605301239776673684415779 907951859665010526623669)
                ·
                  refine ⟨85120486843594736870969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 907951859665010526623669 85120486843594736870969)
                  ·
                    rfl

theorem cell20_186493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_186493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186493 prefixEnd_186493 := by exact prefixLift 186493
  have htrace : WordTrace (prefixWord ++ tailWord_186493) baseStart_186493 baseEnd_186493 := by
    simpa [prefixWord, tailWord_186493, baseEnd_186493] using wordTrace_append hprefix tailTrace_186493
  have hstable : (prefixWord ++ tailWord_186493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186493).length < 2 ^ (prefixWord ++ tailWord_186493).sum := by decide
  have hdescent : baseEnd_186493 < baseStart_186493 := by decide
  rcases family_descends (prefixWord ++ tailWord_186493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186520 : List Nat := [2, 1, 2, 4, 4, 1, 2, 4]
def baseStart_186520 : Nat := 118140960795 + 186520 * 2 ^ 59
def prefixEnd_186520 : Nat := 4983230072969 + 3 ^ 40 * 186520 * 2
def baseEnd_186520 : Nat := 28377603459767547656953

theorem tailTrace_186520 : CollatzResearch.WordTrace tailWord_186520 prefixEnd_186520 28377603459767547656953 := by
  unfold tailWord_186520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3401471642138684962498507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4535295522851579949998009 3401471642138684962498507)
  ·
    refine ⟨5102207463208027443747761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3401471642138684962498507 5102207463208027443747761)
    ·
      refine ⟨3826655597406020582810821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5102207463208027443747761 3826655597406020582810821)
      ·
        refine ⟨717497924513628859277029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3826655597406020582810821 717497924513628859277029)
        ·
          refine ⟨134530860846305411114443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 717497924513628859277029 134530860846305411114443)
          ·
            refine ⟨201796291269458116671665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134530860846305411114443 201796291269458116671665)
            ·
              refine ⟨151347218452093587503749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201796291269458116671665 151347218452093587503749)
              ·
                refine ⟨28377603459767547656953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151347218452093587503749 28377603459767547656953)
                ·
                  rfl

theorem cell20_186520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_186520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186520 prefixEnd_186520 := by exact prefixLift 186520
  have htrace : WordTrace (prefixWord ++ tailWord_186520) baseStart_186520 baseEnd_186520 := by
    simpa [prefixWord, tailWord_186520, baseEnd_186520] using wordTrace_append hprefix tailTrace_186520
  have hstable : (prefixWord ++ tailWord_186520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186520).length < 2 ^ (prefixWord ++ tailWord_186520).sum := by decide
  have hdescent : baseEnd_186520 < baseStart_186520 := by decide
  rcases family_descends (prefixWord ++ tailWord_186520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186552 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_186552 : Nat := 118140960795 + 186552 * 2 ^ 59
def prefixEnd_186552 : Nat := 4983230072969 + 3 ^ 40 * 186552 * 2
def baseEnd_186552 : Nat := 85147416051252753904061

theorem tailTrace_186552 : CollatzResearch.WordTrace tailWord_186552 prefixEnd_186552 85147416051252753904061 := by
  unfold tailWord_186552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3402055210080719695080955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4536073613440959593441273 3402055210080719695080955)
  ·
    refine ⟨5103082815121079542621433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3402055210080719695080955 5103082815121079542621433)
    ·
      refine ⟨3827312111340809656966075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5103082815121079542621433 3827312111340809656966075)
      ·
        refine ⟨5740968167011214485449113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3827312111340809656966075 5740968167011214485449113)
        ·
          refine ⟨4305726125258410864086835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5740968167011214485449113 4305726125258410864086835)
          ·
            refine ⟨6458589187887616296130253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4305726125258410864086835 6458589187887616296130253)
            ·
              refine ⟨2421970945457856111048845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6458589187887616296130253 2421970945457856111048845)
              ·
                refine ⟨908239104546696041643317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2421970945457856111048845 908239104546696041643317)
                ·
                  refine ⟨85147416051252753904061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 908239104546696041643317 85147416051252753904061)
                  ·
                    rfl

theorem cell20_186552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_186552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186552 prefixEnd_186552 := by exact prefixLift 186552
  have htrace : WordTrace (prefixWord ++ tailWord_186552) baseStart_186552 baseEnd_186552 := by
    simpa [prefixWord, tailWord_186552, baseEnd_186552] using wordTrace_append hprefix tailTrace_186552
  have hstable : (prefixWord ++ tailWord_186552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186552).length < 2 ^ (prefixWord ++ tailWord_186552).sum := by decide
  have hdescent : baseEnd_186552 < baseStart_186552 := by decide
  rcases family_descends (prefixWord ++ tailWord_186552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186561 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 3]
def baseStart_186561 : Nat := 118140960795 + 186561 * 2 ^ 59
def prefixEnd_186561 : Nat := 4983230072969 + 3 ^ 40 * 186561 * 2
def baseEnd_186561 : Nat := 85151523896488722604025

theorem tailTrace_186561 : CollatzResearch.WordTrace tailWord_186561 prefixEnd_186561 85151523896488722604025 := by
  unfold tailWord_186561
  simp only [CollatzResearch.WordTrace]
  refine ⟨6804438677128833927239537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4536292451419222618159691 6804438677128833927239537)
  ·
    refine ⟨5103329007846625445429653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6804438677128833927239537 5103329007846625445429653)
    ·
      refine ⟨239218547242810567754515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5103329007846625445429653 239218547242810567754515)
      ·
        refine ⟨358827820864215851631773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239218547242810567754515 358827820864215851631773)
        ·
          refine ⟨134560432824080944361915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358827820864215851631773 134560432824080944361915)
          ·
            refine ⟨201840649236121416542873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134560432824080944361915 201840649236121416542873)
            ·
              refine ⟨151380486927091062407155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201840649236121416542873 151380486927091062407155)
              ·
                refine ⟨227070730390636593610733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151380486927091062407155 227070730390636593610733)
                ·
                  refine ⟨85151523896488722604025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227070730390636593610733 85151523896488722604025)
                  ·
                    rfl

theorem cell20_186561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 3].length) (baseStart_186561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186561 prefixEnd_186561 := by exact prefixLift 186561
  have htrace : WordTrace (prefixWord ++ tailWord_186561) baseStart_186561 baseEnd_186561 := by
    simpa [prefixWord, tailWord_186561, baseEnd_186561] using wordTrace_append hprefix tailTrace_186561
  have hstable : (prefixWord ++ tailWord_186561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186561).length < 2 ^ (prefixWord ++ tailWord_186561).sum := by decide
  have hdescent : baseEnd_186561 < baseStart_186561 := by decide
  rcases family_descends (prefixWord ++ tailWord_186561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186593 : List Nat := [1, 2, 3, 1, 3, 1, 2, 5, 2]
def baseStart_186593 : Nat := 118140960795 + 186593 * 2 ^ 59
def prefixEnd_186593 : Nat := 4983230072969 + 3 ^ 40 * 186593 * 2
def baseEnd_186593 : Nat := 85166129568438833537227

theorem tailTrace_186593 : CollatzResearch.WordTrace tailWord_186593 prefixEnd_186593 85166129568438833537227 := by
  unfold tailWord_186593
  simp only [CollatzResearch.WordTrace]
  refine ⟨6805605813012903392404433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4537070542008602261602955 6805605813012903392404433)
  ·
    refine ⟨5104204359759677544303325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6805605813012903392404433 5104204359759677544303325)
    ·
      refine ⟨1914076634909879079113747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5104204359759677544303325 1914076634909879079113747)
      ·
        refine ⟨2871114952364818618670621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914076634909879079113747 2871114952364818618670621)
        ·
          refine ⟨1076668107136806982001483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2871114952364818618670621 1076668107136806982001483)
          ·
            refine ⟨1615002160705210473002225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076668107136806982001483 1615002160705210473002225)
            ·
              refine ⟨1211251620528907854751669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615002160705210473002225 1211251620528907854751669)
              ·
                refine ⟨113554839424585111382969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1211251620528907854751669 113554839424585111382969)
                ·
                  refine ⟨85166129568438833537227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113554839424585111382969 85166129568438833537227)
                  ·
                    rfl

theorem cell20_186593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 2].length) (baseStart_186593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186593 prefixEnd_186593 := by exact prefixLift 186593
  have htrace : WordTrace (prefixWord ++ tailWord_186593) baseStart_186593 baseEnd_186593 := by
    simpa [prefixWord, tailWord_186593, baseEnd_186593] using wordTrace_append hprefix tailTrace_186593
  have hstable : (prefixWord ++ tailWord_186593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186593).length < 2 ^ (prefixWord ++ tailWord_186593).sum := by decide
  have hdescent : baseEnd_186593 < baseStart_186593 := by decide
  rcases family_descends (prefixWord ++ tailWord_186593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186607 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 3]
def baseStart_186607 : Nat := 118140960795 + 186607 * 2 ^ 59
def prefixEnd_186607 : Nat := 4983230072969 + 3 ^ 40 * 186607 * 2
def baseEnd_186607 : Nat := 85172519549917007070503

theorem tailTrace_186607 : CollatzResearch.WordTrace tailWord_186607 prefixEnd_186607 85172519549917007070503 := by
  unfold tailWord_186607
  simp only [CollatzResearch.WordTrace]
  refine ⟨6806116434962183783414075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4537410956641455855609383 6806116434962183783414075)
  ·
    refine ⟨10209174652443275675121113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6806116434962183783414075 10209174652443275675121113)
    ·
      refine ⟨7656880989332456756340835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10209174652443275675121113 7656880989332456756340835)
      ·
        refine ⟨11485321483998685134511253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7656880989332456756340835 11485321483998685134511253)
        ·
          refine ⟨538374444562438365680215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11485321483998685134511253 538374444562438365680215)
          ·
            refine ⟨807561666843657548520323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538374444562438365680215 807561666843657548520323)
            ·
              refine ⟨1211342500265486322780485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807561666843657548520323 1211342500265486322780485)
              ·
                refine ⟨227126718799778685521341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1211342500265486322780485 227126718799778685521341)
                ·
                  refine ⟨85172519549917007070503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227126718799778685521341 85172519549917007070503)
                  ·
                    rfl

theorem cell20_186607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 3].length) (baseStart_186607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186607 prefixEnd_186607 := by exact prefixLift 186607
  have htrace : WordTrace (prefixWord ++ tailWord_186607) baseStart_186607 baseEnd_186607 := by
    simpa [prefixWord, tailWord_186607, baseEnd_186607] using wordTrace_append hprefix tailTrace_186607
  have hstable : (prefixWord ++ tailWord_186607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186607).length < 2 ^ (prefixWord ++ tailWord_186607).sum := by decide
  have hdescent : baseEnd_186607 < baseStart_186607 := by decide
  rcases family_descends (prefixWord ++ tailWord_186607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186610 : List Nat := [3, 2, 1, 3, 2, 2, 1, 4, 2]
def baseStart_186610 : Nat := 118140960795 + 186610 * 2 ^ 59
def prefixEnd_186610 : Nat := 4983230072969 + 3 ^ 40 * 186610 * 2
def baseEnd_186610 : Nat := 85173888831662329970491

theorem tailTrace_186610 : CollatzResearch.WordTrace tailWord_186610 prefixEnd_186610 85173888831662329970491 := by
  unfold tailWord_186610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701556463487828823943321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4537483902634210197182189 1701556463487828823943321)
  ·
    refine ⟨1276167347615871617957491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1701556463487828823943321 1276167347615871617957491)
    ·
      refine ⟨1914251021423807426936237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276167347615871617957491 1914251021423807426936237)
      ·
        refine ⟨717844133033927785101089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1914251021423807426936237 717844133033927785101089)
        ·
          refine ⟨538383099775445838825817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717844133033927785101089 538383099775445838825817)
          ·
            refine ⟨403787324831584379119363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538383099775445838825817 403787324831584379119363)
            ·
              refine ⟨605680987247376568679045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403787324831584379119363 605680987247376568679045)
              ·
                refine ⟨113565185108883106627321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 605680987247376568679045 113565185108883106627321)
                ·
                  refine ⟨85173888831662329970491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113565185108883106627321 85173888831662329970491)
                  ·
                    rfl

theorem cell20_186610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_186610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186610 prefixEnd_186610 := by exact prefixLift 186610
  have htrace : WordTrace (prefixWord ++ tailWord_186610) baseStart_186610 baseEnd_186610 := by
    simpa [prefixWord, tailWord_186610, baseEnd_186610] using wordTrace_append hprefix tailTrace_186610
  have hstable : (prefixWord ++ tailWord_186610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186610).length < 2 ^ (prefixWord ++ tailWord_186610).sum := by decide
  have hdescent : baseEnd_186610 < baseStart_186610 := by decide
  rcases family_descends (prefixWord ++ tailWord_186610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186638 : List Nat := [4, 1, 1, 2, 1, 2, 5, 4]
def baseStart_186638 : Nat := 118140960795 + 186638 * 2 ^ 59
def prefixEnd_186638 : Nat := 4983230072969 + 3 ^ 40 * 186638 * 2
def baseEnd_186638 : Nat := 28395556264872892345681

theorem tailTrace_186638 : CollatzResearch.WordTrace tailWord_186638 prefixEnd_186638 28395556264872892345681 := by
  unfold tailWord_186638
  simp only [CollatzResearch.WordTrace]
  refine ⟨850905887231234509724071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4538164731899917385195045 850905887231234509724071)
  ·
    refine ⟨1276358830846851764586107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 850905887231234509724071 1276358830846851764586107)
    ·
      refine ⟨1914538246270277646879161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276358830846851764586107 1914538246270277646879161)
      ·
        refine ⟨1435903684702708235159371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1914538246270277646879161 1435903684702708235159371)
        ·
          refine ⟨2153855527054062352739057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435903684702708235159371 2153855527054062352739057)
          ·
            refine ⟨1615391645290546764554293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2153855527054062352739057 1615391645290546764554293)
            ·
              refine ⟨151442966745988759176965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1615391645290546764554293 151442966745988759176965)
              ·
                refine ⟨28395556264872892345681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151442966745988759176965 28395556264872892345681)
                ·
                  rfl

theorem cell20_186638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_186638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186638 prefixEnd_186638 := by exact prefixLift 186638
  have htrace : WordTrace (prefixWord ++ tailWord_186638) baseStart_186638 baseEnd_186638 := by
    simpa [prefixWord, tailWord_186638, baseEnd_186638] using wordTrace_append hprefix tailTrace_186638
  have hstable : (prefixWord ++ tailWord_186638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186638).length < 2 ^ (prefixWord ++ tailWord_186638).sum := by decide
  have hdescent : baseEnd_186638 < baseStart_186638 := by decide
  rcases family_descends (prefixWord ++ tailWord_186638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186704 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_186704 : Nat := 118140960795 + 186704 * 2 ^ 59
def prefixEnd_186704 : Nat := 4983230072969 + 3 ^ 40 * 186704 * 2
def baseEnd_186704 : Nat := 85216792993015780836773

theorem tailTrace_186704 : CollatzResearch.WordTrace tailWord_186704 prefixEnd_186704 85216792993015780836773 := by
  unfold tailWord_186704
  simp only [CollatzResearch.WordTrace]
  refine ⟨3404827157805384674847583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4539769543740512899796777 3404827157805384674847583)
  ·
    refine ⟨5107240736708077012271375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3404827157805384674847583 5107240736708077012271375)
    ·
      refine ⟨7660861105062115518407063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5107240736708077012271375 7660861105062115518407063)
      ·
        refine ⟨11491291657593173277610595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7660861105062115518407063 11491291657593173277610595)
        ·
          refine ⟨17236937486389759916415893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11491291657593173277610595 17236937486389759916415893)
          ·
            refine ⟨807981444674519996081995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17236937486389759916415893 807981444674519996081995)
            ·
              refine ⟨1211972167011779994122993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807981444674519996081995 1211972167011779994122993)
              ·
                refine ⟨908979125258834995592245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211972167011779994122993 908979125258834995592245)
                ·
                  refine ⟨85216792993015780836773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 908979125258834995592245 85216792993015780836773)
                  ·
                    rfl

theorem cell20_186704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_186704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186704 prefixEnd_186704 := by exact prefixLift 186704
  have htrace : WordTrace (prefixWord ++ tailWord_186704) baseStart_186704 baseEnd_186704 := by
    simpa [prefixWord, tailWord_186704, baseEnd_186704] using wordTrace_append hprefix tailTrace_186704
  have hstable : (prefixWord ++ tailWord_186704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186704).length < 2 ^ (prefixWord ++ tailWord_186704).sum := by decide
  have hdescent : baseEnd_186704 < baseStart_186704 := by decide
  rcases family_descends (prefixWord ++ tailWord_186704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186724 : List Nat := [2, 3, 1, 1, 3, 1, 5, 2, 2]
def baseStart_186724 : Nat := 118140960795 + 186724 * 2 ^ 59
def prefixEnd_186724 : Nat := 4983230072969 + 3 ^ 40 * 186724 * 2
def baseEnd_186724 : Nat := 85225921537984600170025

theorem tailTrace_186724 : CollatzResearch.WordTrace tailWord_186724 prefixEnd_186724 85225921537984600170025 := by
  unfold tailWord_186724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3405191887769156382711613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4540255850358875176948817 3405191887769156382711613)
  ·
    refine ⟨1276946957913433643516855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3405191887769156382711613 1276946957913433643516855)
    ·
      refine ⟨1915420436870150465275283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276946957913433643516855 1915420436870150465275283)
      ·
        refine ⟨2873130655305225697912925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915420436870150465275283 2873130655305225697912925)
        ·
          refine ⟨1077423995739459636717347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2873130655305225697912925 1077423995739459636717347)
          ·
            refine ⟨1616135993609189455076021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077423995739459636717347 1616135993609189455076021)
            ·
              refine ⟨151512749400861511413377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1616135993609189455076021 151512749400861511413377)
              ·
                refine ⟨113634562050646133560033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151512749400861511413377 113634562050646133560033)
                ·
                  refine ⟨85225921537984600170025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113634562050646133560033 85225921537984600170025)
                  ·
                    rfl

theorem cell20_186724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_186724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186724 prefixEnd_186724 := by exact prefixLift 186724
  have htrace : WordTrace (prefixWord ++ tailWord_186724) baseStart_186724 baseEnd_186724 := by
    simpa [prefixWord, tailWord_186724, baseEnd_186724] using wordTrace_append hprefix tailTrace_186724
  have hstable : (prefixWord ++ tailWord_186724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186724).length < 2 ^ (prefixWord ++ tailWord_186724).sum := by decide
  have hdescent : baseEnd_186724 < baseStart_186724 := by decide
  rcases family_descends (prefixWord ++ tailWord_186724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186738 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_186738 : Nat := 118140960795 + 186738 * 2 ^ 59
def prefixEnd_186738 : Nat := 4983230072969 + 3 ^ 40 * 186738 * 2
def baseEnd_186738 : Nat := 85232311519462773703301

theorem tailTrace_186738 : CollatzResearch.WordTrace tailWord_186738 prefixEnd_186738 85232311519462773703301 := by
  unfold tailWord_186738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702723599371898289108217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4540596264991728770955245 1702723599371898289108217)
  ·
    refine ⟨1277042699528923716831163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1702723599371898289108217 1277042699528923716831163)
    ·
      refine ⟨1915564049293385575246745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1277042699528923716831163 1915564049293385575246745)
      ·
        refine ⟨1436673036970039181435059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1915564049293385575246745 1436673036970039181435059)
        ·
          refine ⟨2155009555455058772152589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436673036970039181435059 2155009555455058772152589)
          ·
            refine ⟨808128583295647039557221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2155009555455058772152589 808128583295647039557221)
            ·
              refine ⟨151524109367933819916979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 808128583295647039557221 151524109367933819916979)
              ·
                refine ⟨227286164051900729875469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151524109367933819916979 227286164051900729875469)
                ·
                  refine ⟨85232311519462773703301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227286164051900729875469 85232311519462773703301)
                  ·
                    rfl

theorem cell20_186738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_186738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186738 prefixEnd_186738 := by exact prefixLift 186738
  have htrace : WordTrace (prefixWord ++ tailWord_186738) baseStart_186738 baseEnd_186738 := by
    simpa [prefixWord, tailWord_186738, baseEnd_186738] using wordTrace_append hprefix tailTrace_186738
  have hstable : (prefixWord ++ tailWord_186738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186738).length < 2 ^ (prefixWord ++ tailWord_186738).sum := by decide
  have hdescent : baseEnd_186738 < baseStart_186738 := by decide
  rcases family_descends (prefixWord ++ tailWord_186738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186776 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 3]
def baseStart_186776 : Nat := 118140960795 + 186776 * 2 ^ 59
def prefixEnd_186776 : Nat := 4983230072969 + 3 ^ 40 * 186776 * 2
def baseEnd_186776 : Nat := 85249655754903530436479

theorem tailTrace_186776 : CollatzResearch.WordTrace tailWord_186776 prefixEnd_186776 85249655754903530436479 := by
  unfold tailWord_186776
  simp only [CollatzResearch.WordTrace]
  refine ⟨3406140185674962823158091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4541520247566617097544121 3406140185674962823158091)
  ·
    refine ⟨5109210278512444234737137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3406140185674962823158091 5109210278512444234737137)
    ·
      refine ⟨3831907708884333176052853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5109210278512444234737137 3831907708884333176052853)
      ·
        refine ⟨359241347707906235254955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3831907708884333176052853 359241347707906235254955)
        ·
          refine ⟨538862021561859352882433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359241347707906235254955 538862021561859352882433)
          ·
            refine ⟨404146516171394514661825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538862021561859352882433 404146516171394514661825)
            ·
              refine ⟨303109887128545885996369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404146516171394514661825 303109887128545885996369)
              ·
                refine ⟨227332415346409414497277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303109887128545885996369 227332415346409414497277)
                ·
                  refine ⟨85249655754903530436479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227332415346409414497277 85249655754903530436479)
                  ·
                    rfl

theorem cell20_186776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_186776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186776 prefixEnd_186776 := by exact prefixLift 186776
  have htrace : WordTrace (prefixWord ++ tailWord_186776) baseStart_186776 baseEnd_186776 := by
    simpa [prefixWord, tailWord_186776, baseEnd_186776] using wordTrace_append hprefix tailTrace_186776
  have hstable : (prefixWord ++ tailWord_186776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186776).length < 2 ^ (prefixWord ++ tailWord_186776).sum := by decide
  have hdescent : baseEnd_186776 < baseStart_186776 := by decide
  rcases family_descends (prefixWord ++ tailWord_186776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186783 : List Nat := [1, 1, 2, 5, 1, 1, 3, 4, 2]
def baseStart_186783 : Nat := 118140960795 + 186783 * 2 ^ 59
def prefixEnd_186783 : Nat := 4983230072969 + 3 ^ 40 * 186783 * 2
def baseEnd_186783 : Nat := 85252850745642617203117

theorem tailTrace_186783 : CollatzResearch.WordTrace tailWord_186783 prefixEnd_186783 85252850745642617203117 := by
  unfold tailWord_186783
  simp only [CollatzResearch.WordTrace]
  refine ⟨6812535682324565841821003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4541690454883043894547335 6812535682324565841821003)
  ·
    refine ⟨10218803523486848762731505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6812535682324565841821003 10218803523486848762731505)
    ·
      refine ⟨7664102642615136572048629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10218803523486848762731505 7664102642615136572048629)
      ·
        refine ⟨718509622745169053629559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7664102642615136572048629 718509622745169053629559)
        ·
          refine ⟨1077764434117753580444339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718509622745169053629559 1077764434117753580444339)
          ·
            refine ⟨1616646651176630370666509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077764434117753580444339 1616646651176630370666509)
            ·
              refine ⟨606242494191236388999941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1616646651176630370666509 606242494191236388999941)
              ·
                refine ⟨113670467660856822937489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606242494191236388999941 113670467660856822937489)
                ·
                  refine ⟨85252850745642617203117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113670467660856822937489 85252850745642617203117)
                  ·
                    rfl

theorem cell20_186783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 2].length) (baseStart_186783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186783 prefixEnd_186783 := by exact prefixLift 186783
  have htrace : WordTrace (prefixWord ++ tailWord_186783) baseStart_186783 baseEnd_186783 := by
    simpa [prefixWord, tailWord_186783, baseEnd_186783] using wordTrace_append hprefix tailTrace_186783
  have hstable : (prefixWord ++ tailWord_186783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186783).length < 2 ^ (prefixWord ++ tailWord_186783).sum := by decide
  have hdescent : baseEnd_186783 < baseStart_186783 := by decide
  rcases family_descends (prefixWord ++ tailWord_186783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186838 : List Nat := [5, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_186838 : Nat := 118140960795 + 186838 * 2 ^ 59
def prefixEnd_186838 : Nat := 4983230072969 + 3 ^ 40 * 186838 * 2
def baseEnd_186838 : Nat := 85277954244306870369559

theorem tailTrace_186838 : CollatzResearch.WordTrace tailWord_186838 prefixEnd_186838 85277954244306870369559 := by
  unfold tailWord_186838
  simp only [CollatzResearch.WordTrace]
  refine ⟨425908856070331889692073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4543027798083540156715445 425908856070331889692073)
  ·
    refine ⟨319431642052748917269055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 425908856070331889692073 319431642052748917269055)
    ·
      refine ⟨479147463079123375903583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319431642052748917269055 479147463079123375903583)
      ·
        refine ⟨718721194618685063855375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479147463079123375903583 718721194618685063855375)
        ·
          refine ⟨1078081791928027595783063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718721194618685063855375 1078081791928027595783063)
          ·
            refine ⟨1617122687892041393674595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078081791928027595783063 1617122687892041393674595)
            ·
              refine ⟨2425684031838062090511893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617122687892041393674595 2425684031838062090511893)
              ·
                refine ⟨113703938992409160492745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2425684031838062090511893 113703938992409160492745)
                ·
                  refine ⟨85277954244306870369559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113703938992409160492745 85277954244306870369559)
                  ·
                    rfl

theorem cell20_186838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_186838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186838 prefixEnd_186838 := by exact prefixLift 186838
  have htrace : WordTrace (prefixWord ++ tailWord_186838) baseStart_186838 baseEnd_186838 := by
    simpa [prefixWord, tailWord_186838, baseEnd_186838] using wordTrace_append hprefix tailTrace_186838
  have hstable : (prefixWord ++ tailWord_186838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186838).length < 2 ^ (prefixWord ++ tailWord_186838).sum := by decide
  have hdescent : baseEnd_186838 < baseStart_186838 := by decide
  rcases family_descends (prefixWord ++ tailWord_186838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186842 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_186842 : Nat := 118140960795 + 186842 * 2 ^ 59
def prefixEnd_186842 : Nat := 4983230072969 + 3 ^ 40 * 186842 * 2
def baseEnd_186842 : Nat := 85279779953300634236209

theorem tailTrace_186842 : CollatzResearch.WordTrace tailWord_186842 prefixEnd_186842 85279779953300634236209 := by
  unfold tailWord_186842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1703671897277704729554695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4543125059407212612145853 1703671897277704729554695)
  ·
    refine ⟨2555507845916557094332043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1703671897277704729554695 2555507845916557094332043)
    ·
      refine ⟨3833261768874835641498065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2555507845916557094332043 3833261768874835641498065)
      ·
        refine ⟨2874946326656126731123549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3833261768874835641498065 2874946326656126731123549)
        ·
          refine ⟨1078104872496047524171331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2874946326656126731123549 1078104872496047524171331)
          ·
            refine ⟨1617157308744071286256997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078104872496047524171331 1617157308744071286256997)
            ·
              refine ⟨303216995389513366173187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1617157308744071286256997 303216995389513366173187)
              ·
                refine ⟨454825493084270049259781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303216995389513366173187 454825493084270049259781)
                ·
                  refine ⟨85279779953300634236209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454825493084270049259781 85279779953300634236209)
                  ·
                    rfl

theorem cell20_186842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_186842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186842 prefixEnd_186842 := by exact prefixLift 186842
  have htrace : WordTrace (prefixWord ++ tailWord_186842) baseStart_186842 baseEnd_186842 := by
    simpa [prefixWord, tailWord_186842, baseEnd_186842] using wordTrace_append hprefix tailTrace_186842
  have hstable : (prefixWord ++ tailWord_186842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186842).length < 2 ^ (prefixWord ++ tailWord_186842).sum := by decide
  have hdescent : baseEnd_186842 < baseStart_186842 := by decide
  rcases family_descends (prefixWord ++ tailWord_186842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186866 : List Nat := [3, 2, 1, 4, 2, 1, 1, 6]
def baseStart_186866 : Nat := 118140960795 + 186866 * 2 ^ 59
def prefixEnd_186866 : Nat := 4983230072969 + 3 ^ 40 * 186866 * 2
def baseEnd_186866 : Nat := 28430244735754405812037

theorem tailTrace_186866 : CollatzResearch.WordTrace tailWord_186866 prefixEnd_186866 28430244735754405812037 := by
  unfold tailWord_186866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1703890735255967754273113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4543708627349247344728301 1703890735255967754273113)
  ·
    refine ⟨1277918051441975815704835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1703890735255967754273113 1277918051441975815704835)
    ·
      refine ⟨1916877077162963723557253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1277918051441975815704835 1916877077162963723557253)
      ·
        refine ⟨359414451968055698166985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1916877077162963723557253 359414451968055698166985)
        ·
          refine ⟨269560838976041773625239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359414451968055698166985 269560838976041773625239)
          ·
            refine ⟨404341258464062660437859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269560838976041773625239 404341258464062660437859)
            ·
              refine ⟨606511887696093990656789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404341258464062660437859 606511887696093990656789)
              ·
                refine ⟨28430244735754405812037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 606511887696093990656789 28430244735754405812037)
                ·
                  rfl

theorem cell20_186866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_186866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186866 prefixEnd_186866 := by exact prefixLift 186866
  have htrace : WordTrace (prefixWord ++ tailWord_186866) baseStart_186866 baseEnd_186866 := by
    simpa [prefixWord, tailWord_186866, baseEnd_186866] using wordTrace_append hprefix tailTrace_186866
  have hstable : (prefixWord ++ tailWord_186866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186866).length < 2 ^ (prefixWord ++ tailWord_186866).sum := by decide
  have hdescent : baseEnd_186866 < baseStart_186866 := by decide
  rcases family_descends (prefixWord ++ tailWord_186866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186893 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 4]
def baseStart_186893 : Nat := 118140960795 + 186893 * 2 ^ 59
def prefixEnd_186893 : Nat := 4983230072969 + 3 ^ 40 * 186893 * 2
def baseEnd_186893 : Nat := 85303057742971123536001

theorem tailTrace_186893 : CollatzResearch.WordTrace tailWord_186893 prefixEnd_186893 85303057742971123536001 := by
  unfold tailWord_186893
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816547711926054628325333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4544365141284036418883555 6816547711926054628325333)
  ·
    refine ⟨159762836998266905351375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 6816547711926054628325333 159762836998266905351375)
    ·
      refine ⟨239644255497400358027063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159762836998266905351375 239644255497400358027063)
      ·
        refine ⟨359466383246100537040595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239644255497400358027063 359466383246100537040595)
        ·
          refine ⟨539199574869150805560893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359466383246100537040595 539199574869150805560893)
          ·
            refine ⟨202199840575931552085335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 539199574869150805560893 202199840575931552085335)
            ·
              refine ⟨303299760863897328128003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202199840575931552085335 303299760863897328128003)
              ·
                refine ⟨454949641295845992192005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303299760863897328128003 454949641295845992192005)
                ·
                  refine ⟨85303057742971123536001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454949641295845992192005 85303057742971123536001)
                  ·
                    rfl

theorem cell20_186893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_186893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186893 prefixEnd_186893 := by exact prefixLift 186893
  have htrace : WordTrace (prefixWord ++ tailWord_186893) baseStart_186893 baseEnd_186893 := by
    simpa [prefixWord, tailWord_186893, baseEnd_186893] using wordTrace_append hprefix tailTrace_186893
  have hstable : (prefixWord ++ tailWord_186893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186893).length < 2 ^ (prefixWord ++ tailWord_186893).sum := by decide
  have hdescent : baseEnd_186893 < baseStart_186893 := by decide
  rcases family_descends (prefixWord ++ tailWord_186893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186942 : List Nat := [4, 2, 1, 4, 1, 8]
def baseStart_186942 : Nat := 118140960795 + 186942 * 2 ^ 59
def prefixEnd_186942 : Nat := 4983230072969 + 3 ^ 40 * 186942 * 2
def baseEnd_186942 : Nat := 3160200839931286329721

theorem tailTrace_186942 : CollatzResearch.WordTrace tailWord_186942 prefixEnd_186942 3160200839931286329721 := by
  unfold tailWord_186942
  simp only [CollatzResearch.WordTrace]
  refine ⟨852291861093566999607385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4545556592499023997906053 852291861093566999607385)
  ·
    refine ⟨639218895820175249705539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 852291861093566999607385 639218895820175249705539)
    ·
      refine ⟨958828343730262874558309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 639218895820175249705539 958828343730262874558309)
      ·
        refine ⟨179780314449424288979683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 958828343730262874558309 179780314449424288979683)
        ·
          refine ⟨269670471674136433469525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179780314449424288979683 269670471674136433469525)
          ·
            refine ⟨3160200839931286329721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 269670471674136433469525 3160200839931286329721)
            ·
              rfl

theorem cell20_186942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 8].length) (baseStart_186942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186942 prefixEnd_186942 := by exact prefixLift 186942
  have htrace : WordTrace (prefixWord ++ tailWord_186942) baseStart_186942 baseEnd_186942 := by
    simpa [prefixWord, tailWord_186942, baseEnd_186942] using wordTrace_append hprefix tailTrace_186942
  have hstable : (prefixWord ++ tailWord_186942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186942).length < 2 ^ (prefixWord ++ tailWord_186942).sum := by decide
  have hdescent : baseEnd_186942 < baseStart_186942 := by decide
  rcases family_descends (prefixWord ++ tailWord_186942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186948 : List Nat := [2, 3, 5, 1, 1, 1, 1, 4, 2]
def baseStart_186948 : Nat := 118140960795 + 186948 * 2 ^ 59
def prefixEnd_186948 : Nat := 4983230072969 + 3 ^ 40 * 186948 * 2
def baseEnd_186948 : Nat := 85328161241635376702443

theorem tailTrace_186948 : CollatzResearch.WordTrace tailWord_186948 prefixEnd_186948 85328161241635376702443 := by
  unfold tailWord_186948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3409276863363399510788749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4545702484484532681051665 3409276863363399510788749)
  ·
    refine ⟨1278478823761274816545781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3409276863363399510788749 1278478823761274816545781)
    ·
      refine ⟨119857389727619514051167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1278478823761274816545781 119857389727619514051167)
      ·
        refine ⟨179786084591429271076751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119857389727619514051167 179786084591429271076751)
        ·
          refine ⟨269679126887143906615127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179786084591429271076751 269679126887143906615127)
          ·
            refine ⟨404518690330715859922691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269679126887143906615127 404518690330715859922691)
            ·
              refine ⟨606778035496073789884037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404518690330715859922691 606778035496073789884037)
              ·
                refine ⟨113770881655513835603257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606778035496073789884037 113770881655513835603257)
                ·
                  refine ⟨85328161241635376702443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113770881655513835603257 85328161241635376702443)
                  ·
                    rfl

theorem cell20_186948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_186948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186948 prefixEnd_186948 := by exact prefixLift 186948
  have htrace : WordTrace (prefixWord ++ tailWord_186948) baseStart_186948 baseEnd_186948 := by
    simpa [prefixWord, tailWord_186948, baseEnd_186948] using wordTrace_append hprefix tailTrace_186948
  have hstable : (prefixWord ++ tailWord_186948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186948).length < 2 ^ (prefixWord ++ tailWord_186948).sum := by decide
  have hdescent : baseEnd_186948 < baseStart_186948 := by decide
  rcases family_descends (prefixWord ++ tailWord_186948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186949 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 3]
def baseStart_186949 : Nat := 118140960795 + 186949 * 2 ^ 59
def prefixEnd_186949 : Nat := 4983230072969 + 3 ^ 40 * 186949 * 2
def baseEnd_186949 : Nat := 85328617668883817669105

theorem tailTrace_186949 : CollatzResearch.WordTrace tailWord_186949 prefixEnd_186949 85328617668883817669105 := by
  unfold tailWord_186949
  simp only [CollatzResearch.WordTrace]
  refine ⟨6818590199723176192363901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4545726799815450794909267 6818590199723176192363901)
  ·
    refine ⟨2556971324896191072136463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6818590199723176192363901 2556971324896191072136463)
    ·
      refine ⟨3835456987344286608204695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2556971324896191072136463 3835456987344286608204695)
      ·
        refine ⟨5753185481016429912307043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3835456987344286608204695 5753185481016429912307043)
        ·
          refine ⟨8629778221524644868460565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5753185481016429912307043 8629778221524644868460565)
          ·
            refine ⟨404520854133967728209089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8629778221524644868460565 404520854133967728209089)
            ·
              refine ⟨303390640600475796156817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404520854133967728209089 303390640600475796156817)
              ·
                refine ⟨227542980450356847117613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303390640600475796156817 227542980450356847117613)
                ·
                  refine ⟨85328617668883817669105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227542980450356847117613 85328617668883817669105)
                  ·
                    rfl

theorem cell20_186949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_186949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186949 prefixEnd_186949 := by exact prefixLift 186949
  have htrace : WordTrace (prefixWord ++ tailWord_186949) baseStart_186949 baseEnd_186949 := by
    simpa [prefixWord, tailWord_186949, baseEnd_186949] using wordTrace_append hprefix tailTrace_186949
  have hstable : (prefixWord ++ tailWord_186949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186949).length < 2 ^ (prefixWord ++ tailWord_186949).sum := by decide
  have hdescent : baseEnd_186949 < baseStart_186949 := by decide
  rcases family_descends (prefixWord ++ tailWord_186949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186977 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 6]
def baseStart_186977 : Nat := 118140960795 + 186977 * 2 ^ 59
def prefixEnd_186977 : Nat := 4983230072969 + 3 ^ 40 * 186977 * 2
def baseEnd_186977 : Nat := 85341397631840164735657

theorem tailTrace_186977 : CollatzResearch.WordTrace tailWord_186977 prefixEnd_186977 85341397631840164735657 := by
  unfold tailWord_186977
  simp only [CollatzResearch.WordTrace]
  refine ⟨6819611443621736974383185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4546407629081157982922123 6819611443621736974383185)
  ·
    refine ⟨5114708582716302730787389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6819611443621736974383185 5114708582716302730787389)
    ·
      refine ⟨1918015718518613524045271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5114708582716302730787389 1918015718518613524045271)
      ·
        refine ⟨2877023577777920286067907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918015718518613524045271 2877023577777920286067907)
        ·
          refine ⟨4315535366666880429101861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877023577777920286067907 4315535366666880429101861)
          ·
            refine ⟨809162881250040080456599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4315535366666880429101861 809162881250040080456599)
            ·
              refine ⟨1213744321875060120684899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809162881250040080456599 1213744321875060120684899)
              ·
                refine ⟨1820616482812590181027349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213744321875060120684899 1820616482812590181027349)
                ·
                  refine ⟨85341397631840164735657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1820616482812590181027349 85341397631840164735657)
                  ·
                    rfl

theorem cell20_186977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_186977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186977 prefixEnd_186977 := by exact prefixLift 186977
  have htrace : WordTrace (prefixWord ++ tailWord_186977) baseStart_186977 baseEnd_186977 := by
    simpa [prefixWord, tailWord_186977, baseEnd_186977] using wordTrace_append hprefix tailTrace_186977
  have hstable : (prefixWord ++ tailWord_186977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186977).length < 2 ^ (prefixWord ++ tailWord_186977).sum := by decide
  have hdescent : baseEnd_186977 < baseStart_186977 := by decide
  rcases family_descends (prefixWord ++ tailWord_186977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186990 : List Nat := [4, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_186990 : Nat := 118140960795 + 186990 * 2 ^ 59
def prefixEnd_186990 : Nat := 4983230072969 + 3 ^ 40 * 186990 * 2
def baseEnd_186990 : Nat := 85347331186069897302271

theorem tailTrace_186990 : CollatzResearch.WordTrace tailWord_186990 prefixEnd_186990 85347331186069897302271 := by
  unfold tailWord_186990
  simp only [CollatzResearch.WordTrace]
  refine ⟨852510699071830024325803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4546723728383093463070949 852510699071830024325803)
  ·
    refine ⟨1278766048607745036488705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 852510699071830024325803 1278766048607745036488705)
    ·
      refine ⟨959074536455808777366529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1278766048607745036488705 959074536455808777366529)
      ·
        refine ⟨719305902341856583024897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 959074536455808777366529 719305902341856583024897)
        ·
          refine ⟨539479426756392437268673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 719305902341856583024897 539479426756392437268673)
          ·
            refine ⟨404609570067294327951505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539479426756392437268673 404609570067294327951505)
            ·
              refine ⟨303457177550470745963629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404609570067294327951505 303457177550470745963629)
              ·
                refine ⟨113796441581426529736361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303457177550470745963629 113796441581426529736361)
                ·
                  refine ⟨85347331186069897302271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113796441581426529736361 85347331186069897302271)
                  ·
                    rfl

theorem cell20_186990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_186990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_186990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_186990 prefixEnd_186990 := by exact prefixLift 186990
  have htrace : WordTrace (prefixWord ++ tailWord_186990) baseStart_186990 baseEnd_186990 := by
    simpa [prefixWord, tailWord_186990, baseEnd_186990] using wordTrace_append hprefix tailTrace_186990
  have hstable : (prefixWord ++ tailWord_186990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186990).length < 2 ^ (prefixWord ++ tailWord_186990).sum := by decide
  have hdescent : baseEnd_186990 < baseStart_186990 := by decide
  rcases family_descends (prefixWord ++ tailWord_186990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187008 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_187008 : Nat := 118140960795 + 187008 * 2 ^ 59
def prefixEnd_187008 : Nat := 4983230072969 + 3 ^ 40 * 187008 * 2
def baseEnd_187008 : Nat := 85355546876541834702197

theorem tailTrace_187008 : CollatzResearch.WordTrace tailWord_187008 prefixEnd_187008 85355546876541834702197 := by
  unfold tailWord_187008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3410371053254714634380839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4547161404339619512507785 3410371053254714634380839)
  ·
    refine ⟨5115556579882071951571259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3410371053254714634380839 5115556579882071951571259)
    ·
      refine ⟨7673334869823107927356889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5115556579882071951571259 7673334869823107927356889)
      ·
        refine ⟨5755001152367330945517667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7673334869823107927356889 5755001152367330945517667)
        ·
          refine ⟨8632501728550996418276501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5755001152367330945517667 8632501728550996418276501)
          ·
            refine ⟨404648518525827957106711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8632501728550996418276501 404648518525827957106711)
            ·
              refine ⟨606972777788741935660067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404648518525827957106711 606972777788741935660067)
              ·
                refine ⟨910459166683112903490101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606972777788741935660067 910459166683112903490101)
                ·
                  refine ⟨85355546876541834702197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 910459166683112903490101 85355546876541834702197)
                  ·
                    rfl

theorem cell20_187008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_187008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187008 prefixEnd_187008 := by exact prefixLift 187008
  have htrace : WordTrace (prefixWord ++ tailWord_187008) baseStart_187008 baseEnd_187008 := by
    simpa [prefixWord, tailWord_187008, baseEnd_187008] using wordTrace_append hprefix tailTrace_187008
  have hstable : (prefixWord ++ tailWord_187008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187008).length < 2 ^ (prefixWord ++ tailWord_187008).sum := by decide
  have hdescent : baseEnd_187008 < baseStart_187008 := by decide
  rcases family_descends (prefixWord ++ tailWord_187008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187062 : List Nat := [5, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_187062 : Nat := 118140960795 + 187062 * 2 ^ 59
def prefixEnd_187062 : Nat := 4983230072969 + 3 ^ 40 * 187062 * 2
def baseEnd_187062 : Nat := 85380193947957646901977

theorem tailTrace_187062 : CollatzResearch.WordTrace tailWord_187062 prefixEnd_187062 85380193947957646901977 := by
  unfold tailWord_187062
  simp only [CollatzResearch.WordTrace]
  refine ⟨426419478019612280701715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4548474432209197660818293 426419478019612280701715)
  ·
    refine ⟨639629217029418421052573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 426419478019612280701715 639629217029418421052573)
    ·
      refine ⟨239860956386031907894715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 639629217029418421052573 239860956386031907894715)
      ·
        refine ⟨359791434579047861842073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239860956386031907894715 359791434579047861842073)
        ·
          refine ⟨269843575934285896381555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359791434579047861842073 269843575934285896381555)
          ·
            refine ⟨404765363901428844572333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269843575934285896381555 404765363901428844572333)
            ·
              refine ⟨151787011463035816714625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404765363901428844572333 151787011463035816714625)
              ·
                refine ⟨113840258597276862535969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151787011463035816714625 113840258597276862535969)
                ·
                  refine ⟨85380193947957646901977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113840258597276862535969 85380193947957646901977)
                  ·
                    rfl

theorem cell20_187062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_187062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187062 prefixEnd_187062 := by exact prefixLift 187062
  have htrace : WordTrace (prefixWord ++ tailWord_187062) baseStart_187062 baseEnd_187062 := by
    simpa [prefixWord, tailWord_187062, baseEnd_187062] using wordTrace_append hprefix tailTrace_187062
  have hstable : (prefixWord ++ tailWord_187062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187062).length < 2 ^ (prefixWord ++ tailWord_187062).sum := by decide
  have hdescent : baseEnd_187062 < baseStart_187062 := by decide
  rcases family_descends (prefixWord ++ tailWord_187062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187073 : List Nat := [1, 2, 6, 2, 1, 1, 2, 5]
def baseStart_187073 : Nat := 118140960795 + 187073 * 2 ^ 59
def prefixEnd_187073 : Nat := 4983230072969 + 3 ^ 40 * 187073 * 2
def baseEnd_187073 : Nat := 28461738215896832511755

theorem tailTrace_187073 : CollatzResearch.WordTrace tailWord_187073 prefixEnd_187073 28461738215896832511755 := by
  unfold tailWord_187073
  simp only [CollatzResearch.WordTrace]
  refine ⟨6823112851273945369877873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4548741900849296913251915 6823112851273945369877873)
  ·
    refine ⟨5117334638455459027408405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6823112851273945369877873 5117334638455459027408405)
    ·
      refine ⟨239875061177599641909769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5117334638455459027408405 239875061177599641909769)
      ·
        refine ⟨179906295883199731432327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239875061177599641909769 179906295883199731432327)
        ·
          refine ⟨269859443824799597148491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179906295883199731432327 269859443824799597148491)
          ·
            refine ⟨404789165737199395722737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269859443824799597148491 404789165737199395722737)
            ·
              refine ⟨303591874302899546792053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404789165737199395722737 303591874302899546792053)
              ·
                refine ⟨28461738215896832511755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 303591874302899546792053 28461738215896832511755)
                ·
                  rfl

theorem cell20_187073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 5].length) (baseStart_187073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187073 prefixEnd_187073 := by exact prefixLift 187073
  have htrace : WordTrace (prefixWord ++ tailWord_187073) baseStart_187073 baseEnd_187073 := by
    simpa [prefixWord, tailWord_187073, baseEnd_187073] using wordTrace_append hprefix tailTrace_187073
  have hstable : (prefixWord ++ tailWord_187073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187073).length < 2 ^ (prefixWord ++ tailWord_187073).sum := by decide
  have hdescent : baseEnd_187073 < baseStart_187073 := by decide
  rcases family_descends (prefixWord ++ tailWord_187073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187080 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 3]
def baseStart_187080 : Nat := 118140960795 + 187080 * 2 ^ 59
def prefixEnd_187080 : Nat := 4983230072969 + 3 ^ 40 * 187080 * 2
def baseEnd_187080 : Nat := 85388409638429584301903

theorem tailTrace_187080 : CollatzResearch.WordTrace tailWord_187080 prefixEnd_187080 85388409638429584301903 := by
  unfold tailWord_187080
  simp only [CollatzResearch.WordTrace]
  refine ⟨3411684081124292782691347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4548912108165723710255129 3411684081124292782691347)
  ·
    refine ⟨5117526121686439174037021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3411684081124292782691347 5117526121686439174037021)
    ·
      refine ⟨1919072295632414690263883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5117526121686439174037021 1919072295632414690263883)
      ·
        refine ⟨2878608443448622035395825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1919072295632414690263883 2878608443448622035395825)
        ·
          refine ⟨2158956332586466526546869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2878608443448622035395825 2158956332586466526546869)
          ·
            refine ⟨202402156179981236863769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2158956332586466526546869 202402156179981236863769)
            ·
              refine ⟨151801617134985927647827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202402156179981236863769 151801617134985927647827)
              ·
                refine ⟨227702425702478891471741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151801617134985927647827 227702425702478891471741)
                ·
                  refine ⟨85388409638429584301903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227702425702478891471741 85388409638429584301903)
                  ·
                    rfl

theorem cell20_187080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_187080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187080 prefixEnd_187080 := by exact prefixLift 187080
  have htrace : WordTrace (prefixWord ++ tailWord_187080) baseStart_187080 baseEnd_187080 := by
    simpa [prefixWord, tailWord_187080, baseEnd_187080] using wordTrace_append hprefix tailTrace_187080
  have hstable : (prefixWord ++ tailWord_187080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187080).length < 2 ^ (prefixWord ++ tailWord_187080).sum := by decide
  have hdescent : baseEnd_187080 < baseStart_187080 := by decide
  rcases family_descends (prefixWord ++ tailWord_187080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187098 : List Nat := [3, 1, 1, 2, 2, 2, 1, 8]
def baseStart_187098 : Nat := 118140960795 + 187098 * 2 ^ 59
def prefixEnd_187098 : Nat := 4983230072969 + 3 ^ 40 * 187098 * 2
def baseEnd_187098 : Nat := 28465541776300507233943

theorem tailTrace_187098 : CollatzResearch.WordTrace tailWord_187098 prefixEnd_187098 28465541776300507233943 := by
  unfold tailWord_187098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706006169045843659884487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4549349784122249759691965 1706006169045843659884487)
  ·
    refine ⟨2559009253568765489826731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1706006169045843659884487 2559009253568765489826731)
    ·
      refine ⟨3838513880353148234740097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2559009253568765489826731 3838513880353148234740097)
      ·
        refine ⟨2878885410264861176055073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3838513880353148234740097 2878885410264861176055073)
        ·
          refine ⟨2159164057698645882041305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2878885410264861176055073 2159164057698645882041305)
          ·
            refine ⟨1619373043273984411530979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2159164057698645882041305 1619373043273984411530979)
            ·
              refine ⟨2429059564910976617296469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619373043273984411530979 2429059564910976617296469)
              ·
                refine ⟨28465541776300507233943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2429059564910976617296469 28465541776300507233943)
                ·
                  rfl

theorem cell20_187098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_187098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187098 prefixEnd_187098 := by exact prefixLift 187098
  have htrace : WordTrace (prefixWord ++ tailWord_187098) baseStart_187098 baseEnd_187098 := by
    simpa [prefixWord, tailWord_187098, baseEnd_187098] using wordTrace_append hprefix tailTrace_187098
  have hstable : (prefixWord ++ tailWord_187098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187098).length < 2 ^ (prefixWord ++ tailWord_187098).sum := by decide
  have hdescent : baseEnd_187098 < baseStart_187098 := by decide
  rcases family_descends (prefixWord ++ tailWord_187098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187194 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_187194 : Nat := 118140960795 + 187194 * 2 ^ 59
def prefixEnd_187194 : Nat := 4983230072969 + 3 ^ 40 * 187194 * 2
def baseEnd_187194 : Nat := 85440442344751854501437

theorem tailTrace_187194 : CollatzResearch.WordTrace tailWord_187194 prefixEnd_187194 85440442344751854501437 := by
  unfold tailWord_187194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706881520958895758758159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4551684055890388690021757 1706881520958895758758159)
  ·
    refine ⟨2560322281438343638137239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1706881520958895758758159 2560322281438343638137239)
    ·
      refine ⟨3840483422157515457205859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2560322281438343638137239 3840483422157515457205859)
      ·
        refine ⟨5760725133236273185808789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3840483422157515457205859 5760725133236273185808789)
        ·
          refine ⟨270033990620450305584787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5760725133236273185808789 270033990620450305584787)
          ·
            refine ⟨405050985930675458377181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270033990620450305584787 405050985930675458377181)
            ·
              refine ⟨151894119724003296891443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 405050985930675458377181 151894119724003296891443)
              ·
                refine ⟨227841179586004945337165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151894119724003296891443 227841179586004945337165)
                ·
                  refine ⟨85440442344751854501437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227841179586004945337165 85440442344751854501437)
                  ·
                    rfl

theorem cell20_187194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_187194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187194 prefixEnd_187194 := by exact prefixLift 187194
  have htrace : WordTrace (prefixWord ++ tailWord_187194) baseStart_187194 baseEnd_187194 := by
    simpa [prefixWord, tailWord_187194, baseEnd_187194] using wordTrace_append hprefix tailTrace_187194
  have hstable : (prefixWord ++ tailWord_187194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187194).length < 2 ^ (prefixWord ++ tailWord_187194).sum := by decide
  have hdescent : baseEnd_187194 < baseStart_187194 := by decide
  rcases family_descends (prefixWord ++ tailWord_187194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187204 : List Nat := [2, 3, 4, 2, 1, 2, 2, 4]
def baseStart_187204 : Nat := 118140960795 + 187204 * 2 ^ 59
def prefixEnd_187204 : Nat := 4983230072969 + 3 ^ 40 * 187204 * 2
def baseEnd_187204 : Nat := 28481668872412088056021

theorem tailTrace_187204 : CollatzResearch.WordTrace tailWord_187204 prefixEnd_187204 28481668872412088056021 := by
  unfold tailWord_187204
  simp only [CollatzResearch.WordTrace]
  refine ⟨3413945406899677371448333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4551927209199569828597777 3413945406899677371448333)
  ·
    refine ⟨1280229527587379014293125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3413945406899677371448333 1280229527587379014293125)
    ·
      refine ⟨240043036422633565179961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1280229527587379014293125 240043036422633565179961)
      ·
        refine ⟨180032277316975173884971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240043036422633565179961 180032277316975173884971)
        ·
          refine ⟨270048415975462760827457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180032277316975173884971 270048415975462760827457)
          ·
            refine ⟨202536311981597070620593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270048415975462760827457 202536311981597070620593)
            ·
              refine ⟨151902233986197802965445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202536311981597070620593 151902233986197802965445)
              ·
                refine ⟨28481668872412088056021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151902233986197802965445 28481668872412088056021)
                ·
                  rfl

theorem cell20_187204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_187204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187204 prefixEnd_187204 := by exact prefixLift 187204
  have htrace : WordTrace (prefixWord ++ tailWord_187204) baseStart_187204 baseEnd_187204 := by
    simpa [prefixWord, tailWord_187204, baseEnd_187204] using wordTrace_append hprefix tailTrace_187204
  have hstable : (prefixWord ++ tailWord_187204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187204).length < 2 ^ (prefixWord ++ tailWord_187204).sum := by decide
  have hdescent : baseEnd_187204 < baseStart_187204 := by decide
  rcases family_descends (prefixWord ++ tailWord_187204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187236 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_187236 : Nat := 118140960795 + 187236 * 2 ^ 59
def prefixEnd_187236 : Nat := 4983230072969 + 3 ^ 40 * 187236 * 2
def baseEnd_187236 : Nat := 85459612289186375101265

theorem tailTrace_187236 : CollatzResearch.WordTrace tailWord_187236 prefixEnd_187236 85459612289186375101265 := by
  unfold tailWord_187236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3414528974841712104030781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4552705299788949472041041 3414528974841712104030781)
  ·
    refine ⟨1280448365565642039011543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3414528974841712104030781 1280448365565642039011543)
    ·
      refine ⟨1920672548348463058517315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280448365565642039011543 1920672548348463058517315)
      ·
        refine ⟨2881008822522694587775973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920672548348463058517315 2881008822522694587775973)
        ·
          refine ⟨540189154223005235207995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2881008822522694587775973 540189154223005235207995)
          ·
            refine ⟨810283731334507852811993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540189154223005235207995 810283731334507852811993)
            ·
              refine ⟨607712798500880889608995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810283731334507852811993 607712798500880889608995)
              ·
                refine ⟨911569197751321334413493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607712798500880889608995 911569197751321334413493)
                ·
                  refine ⟨85459612289186375101265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 911569197751321334413493 85459612289186375101265)
                  ·
                    rfl

theorem cell20_187236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_187236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187236 prefixEnd_187236 := by exact prefixLift 187236
  have htrace : WordTrace (prefixWord ++ tailWord_187236) baseStart_187236 baseEnd_187236 := by
    simpa [prefixWord, tailWord_187236, baseEnd_187236] using wordTrace_append hprefix tailTrace_187236
  have hstable : (prefixWord ++ tailWord_187236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187236).length < 2 ^ (prefixWord ++ tailWord_187236).sum := by decide
  have hdescent : baseEnd_187236 < baseStart_187236 := by decide
  rcases family_descends (prefixWord ++ tailWord_187236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187243 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 4]
def baseStart_187243 : Nat := 118140960795 + 187243 * 2 ^ 59
def prefixEnd_187243 : Nat := 4983230072969 + 3 ^ 40 * 187243 * 2
def baseEnd_187243 : Nat := 85462807279925461867903

theorem tailTrace_187243 : CollatzResearch.WordTrace tailWord_187243 prefixEnd_187243 85462807279925461867903 := by
  unfold tailWord_187243
  simp only [CollatzResearch.WordTrace]
  refine ⟨6829313260658064403566383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4552875507105376269044255 6829313260658064403566383)
  ·
    refine ⟨10243969890987096605349575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6829313260658064403566383 10243969890987096605349575)
    ·
      refine ⟨15365954836480644908024363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10243969890987096605349575 15365954836480644908024363)
      ·
        refine ⟨23048932254720967362036545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15365954836480644908024363 23048932254720967362036545)
        ·
          refine ⟨17286699191040725521527409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23048932254720967362036545 17286699191040725521527409)
          ·
            refine ⟨12965024393280544141145557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17286699191040725521527409 12965024393280544141145557)
            ·
              refine ⟨303867759217512753308099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12965024393280544141145557 303867759217512753308099)
              ·
                refine ⟨455801638826269129962149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303867759217512753308099 455801638826269129962149)
                ·
                  refine ⟨85462807279925461867903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 455801638826269129962149 85462807279925461867903)
                  ·
                    rfl

theorem cell20_187243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_187243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187243 prefixEnd_187243 := by exact prefixLift 187243
  have htrace : WordTrace (prefixWord ++ tailWord_187243) baseStart_187243 baseEnd_187243 := by
    simpa [prefixWord, tailWord_187243, baseEnd_187243] using wordTrace_append hprefix tailTrace_187243
  have hstable : (prefixWord ++ tailWord_187243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187243).length < 2 ^ (prefixWord ++ tailWord_187243).sum := by decide
  have hdescent : baseEnd_187243 < baseStart_187243 := by decide
  rcases family_descends (prefixWord ++ tailWord_187243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187246 : List Nat := [4, 1, 2, 3, 2, 1, 2, 5]
def baseStart_187246 : Nat := 118140960795 + 187246 * 2 ^ 59
def prefixEnd_187246 : Nat := 4983230072969 + 3 ^ 40 * 187246 * 2
def baseEnd_187246 : Nat := 28488058853890261589297

theorem tailTrace_187246 : CollatzResearch.WordTrace tailWord_187246 prefixEnd_187246 28488058853890261589297 := by
  unfold tailWord_187246
  simp only [CollatzResearch.WordTrace]
  refine ⟨853677834955899489490699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4552948453098130610617061 853677834955899489490699)
  ·
    refine ⟨1280516752433849234236049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853677834955899489490699 1280516752433849234236049)
    ·
      refine ⟨960387564325386925677037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1280516752433849234236049 960387564325386925677037)
      ·
        refine ⟨360145336622020097128889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 960387564325386925677037 360145336622020097128889)
        ·
          refine ⟨270109002466515072846667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360145336622020097128889 270109002466515072846667)
          ·
            refine ⟨405163503699772609270001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270109002466515072846667 405163503699772609270001)
            ·
              refine ⟨303872627774829456952501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405163503699772609270001 303872627774829456952501)
              ·
                refine ⟨28488058853890261589297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 303872627774829456952501 28488058853890261589297)
                ·
                  rfl

theorem cell20_187246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_187246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187246 prefixEnd_187246 := by exact prefixLift 187246
  have htrace : WordTrace (prefixWord ++ tailWord_187246) baseStart_187246 baseEnd_187246 := by
    simpa [prefixWord, tailWord_187246, baseEnd_187246] using wordTrace_append hprefix tailTrace_187246
  have hstable : (prefixWord ++ tailWord_187246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187246).length < 2 ^ (prefixWord ++ tailWord_187246).sum := by decide
  have hdescent : baseEnd_187246 < baseStart_187246 := by decide
  rcases family_descends (prefixWord ++ tailWord_187246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187250 : List Nat := [3, 2, 1, 2, 1, 1, 3, 7]
def baseStart_187250 : Nat := 118140960795 + 187250 * 2 ^ 59
def prefixEnd_187250 : Nat := 4983230072969 + 3 ^ 40 * 187250 * 2
def baseEnd_187250 : Nat := 28488667423554849544847

theorem tailTrace_187250 : CollatzResearch.WordTrace tailWord_187250 prefixEnd_187250 28488667423554849544847 := by
  unfold tailWord_187250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707392142908176149767801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4553045714421803066047469 1707392142908176149767801)
  ·
    refine ⟨1280544107181132112325851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1707392142908176149767801 1280544107181132112325851)
    ·
      refine ⟨1920816160771698168488777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280544107181132112325851 1920816160771698168488777)
      ·
        refine ⟨1440612120578773626366583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1920816160771698168488777 1440612120578773626366583)
        ·
          refine ⟨2160918180868160439549875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440612120578773626366583 2160918180868160439549875)
          ·
            refine ⟨3241377271302240659324813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160918180868160439549875 3241377271302240659324813)
            ·
              refine ⟨1215516476738340247246805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3241377271302240659324813 1215516476738340247246805)
              ·
                refine ⟨28488667423554849544847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1215516476738340247246805 28488667423554849544847)
                ·
                  rfl

theorem cell20_187250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_187250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187250 prefixEnd_187250 := by exact prefixLift 187250
  have htrace : WordTrace (prefixWord ++ tailWord_187250) baseStart_187250 baseEnd_187250 := by
    simpa [prefixWord, tailWord_187250, baseEnd_187250] using wordTrace_append hprefix tailTrace_187250
  have hstable : (prefixWord ++ tailWord_187250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187250).length < 2 ^ (prefixWord ++ tailWord_187250).sum := by decide
  have hdescent : baseEnd_187250 < baseStart_187250 := by decide
  rcases family_descends (prefixWord ++ tailWord_187250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187253 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 3]
def baseStart_187253 : Nat := 118140960795 + 187253 * 2 ^ 59
def prefixEnd_187253 : Nat := 4983230072969 + 3 ^ 40 * 187253 * 2
def baseEnd_187253 : Nat := 85467371552409871534529

theorem tailTrace_187253 : CollatzResearch.WordTrace tailWord_187253 prefixEnd_187253 85467371552409871534529 := by
  unfold tailWord_187253
  simp only [CollatzResearch.WordTrace]
  refine ⟨6829677990621836111430413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4553118660414557407620275 6829677990621836111430413)
  ·
    refine ⟨2561129246483188541786405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6829677990621836111430413 2561129246483188541786405)
    ·
      refine ⟨480211733715597851584951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2561129246483188541786405 480211733715597851584951)
      ·
        refine ⟨720317600573396777377427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480211733715597851584951 720317600573396777377427)
        ·
          refine ⟨1080476400860095166066141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720317600573396777377427 1080476400860095166066141)
          ·
            refine ⟨405178650322535687274803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1080476400860095166066141 405178650322535687274803)
            ·
              refine ⟨607767975483803530912205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405178650322535687274803 607767975483803530912205)
              ·
                refine ⟨227912990806426324092077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 607767975483803530912205 227912990806426324092077)
                ·
                  refine ⟨85467371552409871534529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227912990806426324092077 85467371552409871534529)
                  ·
                    rfl

theorem cell20_187253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_187253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187253 prefixEnd_187253 := by exact prefixLift 187253
  have htrace : WordTrace (prefixWord ++ tailWord_187253) baseStart_187253 baseEnd_187253 := by
    simpa [prefixWord, tailWord_187253, baseEnd_187253] using wordTrace_append hprefix tailTrace_187253
  have hstable : (prefixWord ++ tailWord_187253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187253).length < 2 ^ (prefixWord ++ tailWord_187253).sum := by decide
  have hdescent : baseEnd_187253 < baseStart_187253 := by decide
  rcases family_descends (prefixWord ++ tailWord_187253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187346 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_187346 : Nat := 118140960795 + 187346 * 2 ^ 59
def prefixEnd_187346 : Nat := 4983230072969 + 3 ^ 40 * 187346 * 2
def baseEnd_187346 : Nat := 85509819286514881434149

theorem tailTrace_187346 : CollatzResearch.WordTrace tailWord_187346 prefixEnd_187346 85509819286514881434149 := by
  unfold tailWord_187346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708267494821228248641473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4555379986189941996377261 1708267494821228248641473)
  ·
    refine ⟨1281200621115921186481105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1708267494821228248641473 1281200621115921186481105)
    ·
      refine ⟨960900465836940889860829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1281200621115921186481105 960900465836940889860829)
      ·
        refine ⟨360337674688852833697811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 960900465836940889860829 360337674688852833697811)
        ·
          refine ⟨540506512033279250546717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360337674688852833697811 540506512033279250546717)
          ·
            refine ⟨202689942012479718955019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 540506512033279250546717 202689942012479718955019)
            ·
              refine ⟨304034913018719578432529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202689942012479718955019 304034913018719578432529)
              ·
                refine ⟨228026184764039683824397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304034913018719578432529 228026184764039683824397)
                ·
                  refine ⟨85509819286514881434149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228026184764039683824397 85509819286514881434149)
                  ·
                    rfl

theorem cell20_187346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_187346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187346 prefixEnd_187346 := by exact prefixLift 187346
  have htrace : WordTrace (prefixWord ++ tailWord_187346) baseStart_187346 baseEnd_187346 := by
    simpa [prefixWord, tailWord_187346, baseEnd_187346] using wordTrace_append hprefix tailTrace_187346
  have hstable : (prefixWord ++ tailWord_187346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187346).length < 2 ^ (prefixWord ++ tailWord_187346).sum := by decide
  have hdescent : baseEnd_187346 < baseStart_187346 := by decide
  rcases family_descends (prefixWord ++ tailWord_187346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187402 : List Nat := [3, 1, 2, 2, 3, 1, 8]
def baseStart_187402 : Nat := 118140960795 + 187402 * 2 ^ 59
def prefixEnd_187402 : Nat := 4983230072969 + 3 ^ 40 * 187402 * 2
def baseEnd_187402 : Nat := 9503931023603063951917

theorem tailTrace_187402 : CollatzResearch.WordTrace tailWord_187402 prefixEnd_187402 9503931023603063951917 := by
  unfold tailWord_187402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708778116770508639651115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4556741644721356372402973 1708778116770508639651115)
  ·
    refine ⟨2563167175155762959476673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708778116770508639651115 2563167175155762959476673)
    ·
      refine ⟨1922375381366822219607505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2563167175155762959476673 1922375381366822219607505)
      ·
        refine ⟨1441781536025116664705629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1922375381366822219607505 1441781536025116664705629)
        ·
          refine ⟨540668076009418749264611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1441781536025116664705629 540668076009418749264611)
          ·
            refine ⟨811002114014128123896917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540668076009418749264611 811002114014128123896917)
            ·
              refine ⟨9503931023603063951917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 811002114014128123896917 9503931023603063951917)
              ·
                rfl

theorem cell20_187402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 8].length) (baseStart_187402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187402 prefixEnd_187402 := by exact prefixLift 187402
  have htrace : WordTrace (prefixWord ++ tailWord_187402) baseStart_187402 baseEnd_187402 := by
    simpa [prefixWord, tailWord_187402, baseEnd_187402] using wordTrace_append hprefix tailTrace_187402
  have hstable : (prefixWord ++ tailWord_187402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187402).length < 2 ^ (prefixWord ++ tailWord_187402).sum := by decide
  have hdescent : baseEnd_187402 < baseStart_187402 := by decide
  rcases family_descends (prefixWord ++ tailWord_187402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187457 : List Nat := [1, 2, 5, 1, 4, 7]
def baseStart_187457 : Nat := 118140960795 + 187457 * 2 ^ 59
def prefixEnd_187457 : Nat := 4983230072969 + 3 ^ 40 * 187457 * 2
def baseEnd_187457 : Nat := 3168906767077475138285

theorem tailTrace_187457 : CollatzResearch.WordTrace tailWord_187457 prefixEnd_187457 3168906767077475138285 := by
  unfold tailWord_187457
  simp only [CollatzResearch.WordTrace]
  refine ⟨6837118481882778951856625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4558078987921852634571083 6837118481882778951856625)
  ·
    refine ⟨5127838861412084213892469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6837118481882778951856625 5127838861412084213892469)
    ·
      refine ⟨480734893257382895052419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5127838861412084213892469 480734893257382895052419)
      ·
        refine ⟨721102339886074342578629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480734893257382895052419 721102339886074342578629)
        ·
          refine ⟨135206688728638939233493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 721102339886074342578629 135206688728638939233493)
          ·
            refine ⟨3168906767077475138285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 135206688728638939233493 3168906767077475138285)
            ·
              rfl

theorem cell20_187457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 7].length) (baseStart_187457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187457 prefixEnd_187457 := by exact prefixLift 187457
  have htrace : WordTrace (prefixWord ++ tailWord_187457) baseStart_187457 baseEnd_187457 := by
    simpa [prefixWord, tailWord_187457, baseEnd_187457] using wordTrace_append hprefix tailTrace_187457
  have hstable : (prefixWord ++ tailWord_187457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187457).length < 2 ^ (prefixWord ++ tailWord_187457).sum := by decide
  have hdescent : baseEnd_187457 < baseStart_187457 := by decide
  rcases family_descends (prefixWord ++ tailWord_187457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187464 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 3]
def baseStart_187464 : Nat := 118140960795 + 187464 * 2 ^ 59
def prefixEnd_187464 : Nat := 4983230072969 + 3 ^ 40 * 187464 * 2
def baseEnd_187464 : Nat := 85563677701830915500333

theorem tailTrace_187464 : CollatzResearch.WordTrace tailWord_187464 prefixEnd_187464 85563677701830915500333 := by
  unfold tailWord_187464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3418686896428709573680723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4558249195238279431574297 3418686896428709573680723)
  ·
    refine ⟨5128030344643064360521085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3418686896428709573680723 5128030344643064360521085)
    ·
      refine ⟨1923011379241149135195407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5128030344643064360521085 1923011379241149135195407)
      ·
        refine ⟨2884517068861723702793111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923011379241149135195407 2884517068861723702793111)
        ·
          refine ⟨4326775603292585554189667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884517068861723702793111 4326775603292585554189667)
          ·
            refine ⟨6490163404938878331284501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326775603292585554189667 6490163404938878331284501)
            ·
              refine ⟨304226409606509921778961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6490163404938878331284501 304226409606509921778961)
              ·
                refine ⟨228169807204882441334221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304226409606509921778961 228169807204882441334221)
                ·
                  refine ⟨85563677701830915500333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228169807204882441334221 85563677701830915500333)
                  ·
                    rfl

theorem cell20_187464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_187464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187464 prefixEnd_187464 := by exact prefixLift 187464
  have htrace : WordTrace (prefixWord ++ tailWord_187464) baseStart_187464 baseEnd_187464 := by
    simpa [prefixWord, tailWord_187464, baseEnd_187464] using wordTrace_append hprefix tailTrace_187464
  have hstable : (prefixWord ++ tailWord_187464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187464).length < 2 ^ (prefixWord ++ tailWord_187464).sum := by decide
  have hdescent : baseEnd_187464 < baseStart_187464 := by decide
  rcases family_descends (prefixWord ++ tailWord_187464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187495 : List Nat := [1, 1, 5, 1, 1, 4, 3, 4]
def baseStart_187495 : Nat := 118140960795 + 187495 * 2 ^ 59
def prefixEnd_187495 : Nat := 4983230072969 + 3 ^ 40 * 187495 * 2
def baseEnd_187495 : Nat := 28525942315510861822291

theorem tailTrace_187495 : CollatzResearch.WordTrace tailWord_187495 prefixEnd_187495 28525942315510861822291 := by
  unfold tailWord_187495
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838504455745111441739939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4559002970496740961159959 6838504455745111441739939)
  ·
    refine ⟨10257756683617667162609909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6838504455745111441739939 10257756683617667162609909)
    ·
      refine ⟨961664689089156296494679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10257756683617667162609909 961664689089156296494679)
      ·
        refine ⟨1442497033633734444742019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 961664689089156296494679 1442497033633734444742019)
        ·
          refine ⟨2163745550450601667113029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1442497033633734444742019 2163745550450601667113029)
          ·
            refine ⟨405702290709487812583693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2163745550450601667113029 405702290709487812583693)
            ·
              refine ⟨152138359016057929718885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 405702290709487812583693 152138359016057929718885)
              ·
                refine ⟨28525942315510861822291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152138359016057929718885 28525942315510861822291)
                ·
                  rfl

theorem cell20_187495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 4].length) (baseStart_187495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187495 prefixEnd_187495 := by exact prefixLift 187495
  have htrace : WordTrace (prefixWord ++ tailWord_187495) baseStart_187495 baseEnd_187495 := by
    simpa [prefixWord, tailWord_187495, baseEnd_187495] using wordTrace_append hprefix tailTrace_187495
  have hstable : (prefixWord ++ tailWord_187495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187495).length < 2 ^ (prefixWord ++ tailWord_187495).sum := by decide
  have hdescent : baseEnd_187495 < baseStart_187495 := by decide
  rcases family_descends (prefixWord ++ tailWord_187495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187523 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 5]
def baseStart_187523 : Nat := 118140960795 + 187523 * 2 ^ 59
def prefixEnd_187523 : Nat := 4983230072969 + 3 ^ 40 * 187523 * 2
def baseEnd_187523 : Nat := 85590606909488932533425

theorem tailTrace_187523 : CollatzResearch.WordTrace tailWord_187523 prefixEnd_187523 85590606909488932533425 := by
  unfold tailWord_187523
  simp only [CollatzResearch.WordTrace]
  refine ⟨6839525699643672223759223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4559683799762448149172815 6839525699643672223759223)
  ·
    refine ⟨10259288549465508335638835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6839525699643672223759223 10259288549465508335638835)
    ·
      refine ⟨15388932824198262503458253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10259288549465508335638835 15388932824198262503458253)
      ·
        refine ⟨5770849809074348438796845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15388932824198262503458253 5770849809074348438796845)
        ·
          refine ⟨2164068678402880664548817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5770849809074348438796845 2164068678402880664548817)
          ·
            refine ⟨1623051508802160498411613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2164068678402880664548817 1623051508802160498411613)
            ·
              refine ⟨608644315800810186904355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1623051508802160498411613 608644315800810186904355)
              ·
                refine ⟨912966473701215280356533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608644315800810186904355 912966473701215280356533)
                ·
                  refine ⟨85590606909488932533425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 912966473701215280356533 85590606909488932533425)
                  ·
                    rfl

theorem cell20_187523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_187523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187523 prefixEnd_187523 := by exact prefixLift 187523
  have htrace : WordTrace (prefixWord ++ tailWord_187523) baseStart_187523 baseEnd_187523 := by
    simpa [prefixWord, tailWord_187523, baseEnd_187523] using wordTrace_append hprefix tailTrace_187523
  have hstable : (prefixWord ++ tailWord_187523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187523).length < 2 ^ (prefixWord ++ tailWord_187523).sum := by decide
  have hdescent : baseEnd_187523 < baseStart_187523 := by decide
  rcases family_descends (prefixWord ++ tailWord_187523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187550 : List Nat := [4, 3, 1, 1, 2, 1, 4, 4]
def baseStart_187550 : Nat := 118140960795 + 187550 * 2 ^ 59
def prefixEnd_187550 : Nat := 4983230072969 + 3 ^ 40 * 187550 * 2
def baseEnd_187550 : Nat := 28534310148398946211105

theorem tailTrace_187550 : CollatzResearch.WordTrace tailWord_187550 prefixEnd_187550 28534310148398946211105 := by
  unfold tailWord_187550
  simp only [CollatzResearch.WordTrace]
  refine ⟨855063808818231979374013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4560340313697237223328069 855063808818231979374013)
  ·
    refine ⟨320648928306836992265255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 855063808818231979374013 320648928306836992265255)
    ·
      refine ⟨480973392460255488397883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320648928306836992265255 480973392460255488397883)
      ·
        refine ⟨721460088690383232596825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480973392460255488397883 721460088690383232596825)
        ·
          refine ⟨541095066517787424447619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 721460088690383232596825 541095066517787424447619)
          ·
            refine ⟨811642599776681136671429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541095066517787424447619 811642599776681136671429)
            ·
              refine ⟨152182987458127713125893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 811642599776681136671429 152182987458127713125893)
              ·
                refine ⟨28534310148398946211105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152182987458127713125893 28534310148398946211105)
                ·
                  rfl

theorem cell20_187550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_187550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187550 prefixEnd_187550 := by exact prefixLift 187550
  have htrace : WordTrace (prefixWord ++ tailWord_187550) baseStart_187550 baseEnd_187550 := by
    simpa [prefixWord, tailWord_187550, baseEnd_187550] using wordTrace_append hprefix tailTrace_187550
  have hstable : (prefixWord ++ tailWord_187550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187550).length < 2 ^ (prefixWord ++ tailWord_187550).sum := by decide
  have hdescent : baseEnd_187550 < baseStart_187550 := by decide
  rcases family_descends (prefixWord ++ tailWord_187550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187699 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 4]
def baseStart_187699 : Nat := 118140960795 + 187699 * 2 ^ 59
def prefixEnd_187699 : Nat := 4983230072969 + 3 ^ 40 * 187699 * 2
def baseEnd_187699 : Nat := 85670938105214542666039

theorem tailTrace_187699 : CollatzResearch.WordTrace tailWord_187699 prefixEnd_187699 85670938105214542666039 := by
  unfold tailWord_187699
  simp only [CollatzResearch.WordTrace]
  refine ⟨6845944947006054282166151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4563963298004036188110767 6845944947006054282166151)
  ·
    refine ⟨10268917420509081423249227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6845944947006054282166151 10268917420509081423249227)
    ·
      refine ⟨15403376130763622134873841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10268917420509081423249227 15403376130763622134873841)
      ·
        refine ⟨11552532098072716601155381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15403376130763622134873841 11552532098072716601155381)
        ·
          refine ⟨1083049884194317181358317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11552532098072716601155381 1083049884194317181358317)
          ·
            refine ⟨406143706572868943009369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1083049884194317181358317 406143706572868943009369)
            ·
              refine ⟨304607779929651707257027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406143706572868943009369 304607779929651707257027)
              ·
                refine ⟨456911669894477560885541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304607779929651707257027 456911669894477560885541)
                ·
                  refine ⟨85670938105214542666039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 456911669894477560885541 85670938105214542666039)
                  ·
                    rfl

theorem cell20_187699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_187699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187699 prefixEnd_187699 := by exact prefixLift 187699
  have htrace : WordTrace (prefixWord ++ tailWord_187699) baseStart_187699 baseEnd_187699 := by
    simpa [prefixWord, tailWord_187699, baseEnd_187699] using wordTrace_append hprefix tailTrace_187699
  have hstable : (prefixWord ++ tailWord_187699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187699).length < 2 ^ (prefixWord ++ tailWord_187699).sum := by decide
  have hdescent : baseEnd_187699 < baseStart_187699 := by decide
  rcases family_descends (prefixWord ++ tailWord_187699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187716 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 4]
def baseStart_187716 : Nat := 118140960795 + 187716 * 2 ^ 59
def prefixEnd_187716 : Nat := 4983230072969 + 3 ^ 40 * 187716 * 2
def baseEnd_187716 : Nat := 85678697368438039099303

theorem tailTrace_187716 : CollatzResearch.WordTrace tailWord_187716 prefixEnd_187716 85678697368438039099303 := by
  unfold tailWord_187716
  simp only [CollatzResearch.WordTrace]
  refine ⟨3423282493972233092767501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4564376658629644123690001 3423282493972233092767501)
  ·
    refine ⟨1283730935239587409787813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3423282493972233092767501 1283730935239587409787813)
    ·
      refine ⟨240699550357422639335215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1283730935239587409787813 240699550357422639335215)
      ·
        refine ⟨361049325536133959002823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240699550357422639335215 361049325536133959002823)
        ·
          refine ⟨541573988304200938504235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361049325536133959002823 541573988304200938504235)
          ·
            refine ⟨812360982456301407756353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541573988304200938504235 812360982456301407756353)
            ·
              refine ⟨609270736842226055817265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812360982456301407756353 609270736842226055817265)
              ·
                refine ⟨456953052631669541862949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609270736842226055817265 456953052631669541862949)
                ·
                  refine ⟨85678697368438039099303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 456953052631669541862949 85678697368438039099303)
                  ·
                    rfl

theorem cell20_187716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_187716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187716 prefixEnd_187716 := by exact prefixLift 187716
  have htrace : WordTrace (prefixWord ++ tailWord_187716) baseStart_187716 baseEnd_187716 := by
    simpa [prefixWord, tailWord_187716, baseEnd_187716] using wordTrace_append hprefix tailTrace_187716
  have hstable : (prefixWord ++ tailWord_187716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187716).length < 2 ^ (prefixWord ++ tailWord_187716).sum := by decide
  have hdescent : baseEnd_187716 < baseStart_187716 := by decide
  rcases family_descends (prefixWord ++ tailWord_187716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187733 : List Nat := [1, 3, 2, 2, 3, 3, 1, 3, 2]
def baseStart_187733 : Nat := 118140960795 + 187733 * 2 ^ 59
def prefixEnd_187733 : Nat := 4983230072969 + 3 ^ 40 * 187733 * 2
def baseEnd_187733 : Nat := 85686456631661535532567

theorem tailTrace_187733 : CollatzResearch.WordTrace tailWord_187733 prefixEnd_187733 85686456631661535532567 := by
  unfold tailWord_187733
  simp only [CollatzResearch.WordTrace]
  refine ⟨6847185028882878088903853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4564790019255252059269235 6847185028882878088903853)
  ·
    refine ⟨2567694385831079283338945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6847185028882878088903853 2567694385831079283338945)
    ·
      refine ⟨1925770789373309462504209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2567694385831079283338945 1925770789373309462504209)
      ·
        refine ⟨1444328092029982096878157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1925770789373309462504209 1444328092029982096878157)
        ·
          refine ⟨541623034511243286329309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1444328092029982096878157 541623034511243286329309)
          ·
            refine ⟨203108637941716232373491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 541623034511243286329309 203108637941716232373491)
            ·
              refine ⟨304662956912574348560237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203108637941716232373491 304662956912574348560237)
              ·
                refine ⟨114248608842215380710089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304662956912574348560237 114248608842215380710089)
                ·
                  refine ⟨85686456631661535532567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114248608842215380710089 85686456631661535532567)
                  ·
                    rfl

theorem cell20_187733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_187733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187733 prefixEnd_187733 := by exact prefixLift 187733
  have htrace : WordTrace (prefixWord ++ tailWord_187733) baseStart_187733 baseEnd_187733 := by
    simpa [prefixWord, tailWord_187733, baseEnd_187733] using wordTrace_append hprefix tailTrace_187733
  have hstable : (prefixWord ++ tailWord_187733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187733).length < 2 ^ (prefixWord ++ tailWord_187733).sum := by decide
  have hdescent : baseEnd_187733 < baseStart_187733 := by decide
  rcases family_descends (prefixWord ++ tailWord_187733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187744 : List Nat := [2, 1, 1, 3, 4, 3, 6]
def baseStart_187744 : Nat := 118140960795 + 187744 * 2 ^ 59
def prefixEnd_187744 : Nat := 4983230072969 + 3 ^ 40 * 187744 * 2
def baseEnd_187744 : Nat := 9521275259043820685095

theorem tailTrace_187744 : CollatzResearch.WordTrace tailWord_187744 prefixEnd_187744 9521275259043820685095 := by
  unfold tailWord_187744
  simp only [CollatzResearch.WordTrace]
  refine ⟨3423793115921513483777143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4565057487895351311702857 3423793115921513483777143)
  ·
    refine ⟨5135689673882270225665715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3423793115921513483777143 5135689673882270225665715)
    ·
      refine ⟨7703534510823405338498573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5135689673882270225665715 7703534510823405338498573)
      ·
        refine ⟨2888825441558777001936965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7703534510823405338498573 2888825441558777001936965)
        ·
          refine ⟨541654770292270687863181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2888825441558777001936965 541654770292270687863181)
          ·
            refine ⟨203120538859601507948693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 541654770292270687863181 203120538859601507948693)
            ·
              refine ⟨9521275259043820685095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 203120538859601507948693 9521275259043820685095)
              ·
                rfl

theorem cell20_187744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 6].length) (baseStart_187744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187744 prefixEnd_187744 := by exact prefixLift 187744
  have htrace : WordTrace (prefixWord ++ tailWord_187744) baseStart_187744 baseEnd_187744 := by
    simpa [prefixWord, tailWord_187744, baseEnd_187744] using wordTrace_append hprefix tailTrace_187744
  have hstable : (prefixWord ++ tailWord_187744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187744).length < 2 ^ (prefixWord ++ tailWord_187744).sum := by decide
  have hdescent : baseEnd_187744 < baseStart_187744 := by decide
  rcases family_descends (prefixWord ++ tailWord_187744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187816 : List Nat := [2, 1, 6, 1, 2, 2, 1, 5]
def baseStart_187816 : Nat := 118140960795 + 187816 * 2 ^ 59
def prefixEnd_187816 : Nat := 4983230072969 + 3 ^ 40 * 187816 * 2
def baseEnd_187816 : Nat := 28574780031094045255187

theorem tailTrace_187816 : CollatzResearch.WordTrace tailWord_187816 prefixEnd_187816 28574780031094045255187 := by
  unfold tailWord_187816
  simp only [CollatzResearch.WordTrace]
  refine ⟨3425106143791091632087651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4566808191721455509450201 3425106143791091632087651)
  ·
    refine ⟨5137659215686637448131477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3425106143791091632087651 5137659215686637448131477)
    ·
      refine ⟨240827775735311130381163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5137659215686637448131477 240827775735311130381163)
      ·
        refine ⟨361241663602966695571745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240827775735311130381163 361241663602966695571745)
        ·
          refine ⟨270931247702225021678809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361241663602966695571745 270931247702225021678809)
          ·
            refine ⟨203198435776668766259107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270931247702225021678809 203198435776668766259107)
            ·
              refine ⟨304797653665003149388661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203198435776668766259107 304797653665003149388661)
              ·
                refine ⟨28574780031094045255187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 304797653665003149388661 28574780031094045255187)
                ·
                  rfl

theorem cell20_187816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_187816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187816 prefixEnd_187816 := by exact prefixLift 187816
  have htrace : WordTrace (prefixWord ++ tailWord_187816) baseStart_187816 baseEnd_187816 := by
    simpa [prefixWord, tailWord_187816, baseEnd_187816] using wordTrace_append hprefix tailTrace_187816
  have hstable : (prefixWord ++ tailWord_187816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187816).length < 2 ^ (prefixWord ++ tailWord_187816).sum := by decide
  have hdescent : baseEnd_187816 < baseStart_187816 := by decide
  rcases family_descends (prefixWord ++ tailWord_187816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187851 : List Nat := [1, 1, 1, 1, 3, 3, 3, 5, 2]
def baseStart_187851 : Nat := 118140960795 + 187851 * 2 ^ 59
def prefixEnd_187851 : Nat := 4983230072969 + 3 ^ 40 * 187851 * 2
def baseEnd_187851 : Nat := 85740315046977569598751

theorem tailTrace_187851 : CollatzResearch.WordTrace tailWord_187851 prefixEnd_187851 85740315046977569598751 := by
  unfold tailWord_187851
  simp only [CollatzResearch.WordTrace]
  refine ⟨6851488842455384241699407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4567659228303589494466271 6851488842455384241699407)
  ·
    refine ⟨10277233263683076362549111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6851488842455384241699407 10277233263683076362549111)
    ·
      refine ⟨15415849895524614543823667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10277233263683076362549111 15415849895524614543823667)
      ·
        refine ⟨23123774843286921815735501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15415849895524614543823667 23123774843286921815735501)
        ·
          refine ⟨8671415566232595680900813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23123774843286921815735501 8671415566232595680900813)
          ·
            refine ⟨3251780837337223380337805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8671415566232595680900813 3251780837337223380337805)
            ·
              refine ⟨1219417814001458767626677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3251780837337223380337805 1219417814001458767626677)
              ·
                refine ⟨114320420062636759465001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1219417814001458767626677 114320420062636759465001)
                ·
                  refine ⟨85740315046977569598751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114320420062636759465001 85740315046977569598751)
                  ·
                    rfl

theorem cell20_187851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 2].length) (baseStart_187851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187851 prefixEnd_187851 := by exact prefixLift 187851
  have htrace : WordTrace (prefixWord ++ tailWord_187851) baseStart_187851 baseEnd_187851 := by
    simpa [prefixWord, tailWord_187851, baseEnd_187851] using wordTrace_append hprefix tailTrace_187851
  have hstable : (prefixWord ++ tailWord_187851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187851).length < 2 ^ (prefixWord ++ tailWord_187851).sum := by decide
  have hdescent : baseEnd_187851 < baseStart_187851 := by decide
  rcases family_descends (prefixWord ++ tailWord_187851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187865 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 5]
def baseStart_187865 : Nat := 118140960795 + 187865 * 2 ^ 59
def prefixEnd_187865 : Nat := 4983230072969 + 3 ^ 40 * 187865 * 2
def baseEnd_187865 : Nat := 85746705028455743132027

theorem tailTrace_187865 : CollatzResearch.WordTrace tailWord_187865 prefixEnd_187865 85746705028455743132027 := by
  unfold tailWord_187865
  simp only [CollatzResearch.WordTrace]
  refine ⟨6851999464404664632709049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4567999642936443088472699 6851999464404664632709049)
  ·
    refine ⟨5138999598303498474531787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6851999464404664632709049 5138999598303498474531787)
    ·
      refine ⟨7708499397455247711797681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5138999598303498474531787 7708499397455247711797681)
      ·
        refine ⟨5781374548091435783848261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7708499397455247711797681 5781374548091435783848261)
        ·
          refine ⟨1084007727767144209471549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5781374548091435783848261 1084007727767144209471549)
          ·
            refine ⟨406502897912679078551831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1084007727767144209471549 406502897912679078551831)
            ·
              refine ⟨609754346869018617827747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406502897912679078551831 609754346869018617827747)
              ·
                refine ⟨914631520303527926741621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609754346869018617827747 914631520303527926741621)
                ·
                  refine ⟨85746705028455743132027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 914631520303527926741621 85746705028455743132027)
                  ·
                    rfl

theorem cell20_187865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_187865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187865 prefixEnd_187865 := by exact prefixLift 187865
  have htrace : WordTrace (prefixWord ++ tailWord_187865) baseStart_187865 baseEnd_187865 := by
    simpa [prefixWord, tailWord_187865, baseEnd_187865] using wordTrace_append hprefix tailTrace_187865
  have hstable : (prefixWord ++ tailWord_187865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187865).length < 2 ^ (prefixWord ++ tailWord_187865).sum := by decide
  have hdescent : baseEnd_187865 < baseStart_187865 := by decide
  rcases family_descends (prefixWord ++ tailWord_187865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187896 : List Nat := [2, 1, 2, 1, 1, 5, 4, 4]
def baseStart_187896 : Nat := 118140960795 + 187896 * 2 ^ 59
def prefixEnd_187896 : Nat := 4983230072969 + 3 ^ 40 * 187896 * 2
def baseEnd_187896 : Nat := 28586951424385804366189

theorem tailTrace_187896 : CollatzResearch.WordTrace tailWord_187896 prefixEnd_187896 28586951424385804366189 := by
  unfold tailWord_187896
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426565063646178463543771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4568753418194904618058361 3426565063646178463543771)
  ·
    refine ⟨5139847595469267695315657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3426565063646178463543771 5139847595469267695315657)
    ·
      refine ⟨3854885696601950771486743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5139847595469267695315657 3854885696601950771486743)
      ·
        refine ⟨5782328544902926157230115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3854885696601950771486743 5782328544902926157230115)
        ·
          refine ⟨8673492817354389235845173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5782328544902926157230115 8673492817354389235845173)
          ·
            refine ⟨813139951626973990860485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8673492817354389235845173 813139951626973990860485)
            ·
              refine ⟨152463740930057623286341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 813139951626973990860485 152463740930057623286341)
              ·
                refine ⟨28586951424385804366189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152463740930057623286341 28586951424385804366189)
                ·
                  rfl

theorem cell20_187896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_187896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187896 prefixEnd_187896 := by exact prefixLift 187896
  have htrace : WordTrace (prefixWord ++ tailWord_187896) baseStart_187896 baseEnd_187896 := by
    simpa [prefixWord, tailWord_187896, baseEnd_187896] using wordTrace_append hprefix tailTrace_187896
  have hstable : (prefixWord ++ tailWord_187896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187896).length < 2 ^ (prefixWord ++ tailWord_187896).sum := by decide
  have hdescent : baseEnd_187896 < baseStart_187896 := by decide
  rcases family_descends (prefixWord ++ tailWord_187896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187937 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 3]
def baseStart_187937 : Nat := 118140960795 + 187937 * 2 ^ 59
def prefixEnd_187937 : Nat := 4983230072969 + 3 ^ 40 * 187937 * 2
def baseEnd_187937 : Nat := 85779567790343492731733

theorem tailTrace_187937 : CollatzResearch.WordTrace tailWord_187937 prefixEnd_187937 85779567790343492731733 := by
  unfold tailWord_187937
  simp only [CollatzResearch.WordTrace]
  refine ⟨6854625520143820929330065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4569750346762547286220043 6854625520143820929330065)
  ·
    refine ⟨5140969140107865696997549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6854625520143820929330065 5140969140107865696997549)
    ·
      refine ⟨1927863427540449636374081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5140969140107865696997549 1927863427540449636374081)
      ·
        refine ⟨1445897570655337227280561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1927863427540449636374081 1445897570655337227280561)
        ·
          refine ⟨1084423177991502920460421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1445897570655337227280561 1084423177991502920460421)
          ·
            refine ⟨203329345873406797586329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1084423177991502920460421 203329345873406797586329)
            ·
              refine ⟨152497009405055098189747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203329345873406797586329 152497009405055098189747)
              ·
                refine ⟨228745514107582647284621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152497009405055098189747 228745514107582647284621)
                ·
                  refine ⟨85779567790343492731733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228745514107582647284621 85779567790343492731733)
                  ·
                    rfl

theorem cell20_187937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_187937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187937 prefixEnd_187937 := by exact prefixLift 187937
  have htrace : WordTrace (prefixWord ++ tailWord_187937) baseStart_187937 baseEnd_187937 := by
    simpa [prefixWord, tailWord_187937, baseEnd_187937] using wordTrace_append hprefix tailTrace_187937
  have hstable : (prefixWord ++ tailWord_187937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187937).length < 2 ^ (prefixWord ++ tailWord_187937).sum := by decide
  have hdescent : baseEnd_187937 < baseStart_187937 := by decide
  rcases family_descends (prefixWord ++ tailWord_187937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187955 : List Nat := [1, 1, 1, 2, 4, 3, 2, 6]
def baseStart_187955 : Nat := 118140960795 + 187955 * 2 ^ 59
def prefixEnd_187955 : Nat := 4983230072969 + 3 ^ 40 * 187955 * 2
def baseEnd_187955 : Nat := 28595927826938476710553

theorem tailTrace_187955 : CollatzResearch.WordTrace tailWord_187955 prefixEnd_187955 28595927826938476710553 := by
  unfold tailWord_187955
  simp only [CollatzResearch.WordTrace]
  refine ⟨6855282034078610003485319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4570188022719073335656879 6855282034078610003485319)
  ·
    refine ⟨10282923051117915005227979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6855282034078610003485319 10282923051117915005227979)
    ·
      refine ⟨15424384576676872507841969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10282923051117915005227979 15424384576676872507841969)
      ·
        refine ⟨11568288432507654380881477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15424384576676872507841969 11568288432507654380881477)
        ·
          refine ⟨2169054081095185196415277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11568288432507654380881477 2169054081095185196415277)
          ·
            refine ⟨813395280410694448655729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2169054081095185196415277 813395280410694448655729)
            ·
              refine ⟨610046460308020836491797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813395280410694448655729 610046460308020836491797)
              ·
                refine ⟨28595927826938476710553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 610046460308020836491797 28595927826938476710553)
                ·
                  rfl

theorem cell20_187955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_187955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187955 prefixEnd_187955 := by exact prefixLift 187955
  have htrace : WordTrace (prefixWord ++ tailWord_187955) baseStart_187955 baseEnd_187955 := by
    simpa [prefixWord, tailWord_187955, baseEnd_187955] using wordTrace_append hprefix tailTrace_187955
  have hstable : (prefixWord ++ tailWord_187955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187955).length < 2 ^ (prefixWord ++ tailWord_187955).sum := by decide
  have hdescent : baseEnd_187955 < baseStart_187955 := by decide
  rcases family_descends (prefixWord ++ tailWord_187955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187972 : List Nat := [2, 3, 5, 10]
def baseStart_187972 : Nat := 118140960795 + 187972 * 2 ^ 59
def prefixEnd_187972 : Nat := 4983230072969 + 3 ^ 40 * 187972 * 2
def baseEnd_187972 : Nat := 353068077135962660761

theorem tailTrace_187972 : CollatzResearch.WordTrace tailWord_187972 prefixEnd_187972 353068077135962660761 := by
  unfold tailWord_187972
  simp only [CollatzResearch.WordTrace]
  refine ⟨3427951037508510953427085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4570601383344681271236113 3427951037508510953427085)
  ·
    refine ⟨1285481639065691607535157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3427951037508510953427085 1285481639065691607535157)
    ·
      refine ⟨120513903662408588206421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1285481639065691607535157 120513903662408588206421)
      ·
        refine ⟨353068077135962660761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 120513903662408588206421 353068077135962660761)
        ·
          rfl

theorem cell20_187972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 10].length) (baseStart_187972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187972 prefixEnd_187972 := by exact prefixLift 187972
  have htrace : WordTrace (prefixWord ++ tailWord_187972) baseStart_187972 baseEnd_187972 := by
    simpa [prefixWord, tailWord_187972, baseEnd_187972] using wordTrace_append hprefix tailTrace_187972
  have hstable : (prefixWord ++ tailWord_187972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187972).length < 2 ^ (prefixWord ++ tailWord_187972).sum := by decide
  have hdescent : baseEnd_187972 < baseStart_187972 := by decide
  rcases family_descends (prefixWord ++ tailWord_187972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187974 : List Nat := [6, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_187974 : Nat := 118140960795 + 187974 * 2 ^ 59
def prefixEnd_187974 : Nat := 4983230072969 + 3 ^ 40 * 187974 * 2
def baseEnd_187974 : Nat := 85796455598535808498249

theorem tailTrace_187974 : CollatzResearch.WordTrace tailWord_187974 prefixEnd_187974 85796455598535808498249 := by
  unfold tailWord_187974
  simp only [CollatzResearch.WordTrace]
  refine ⟨214249219406555507763343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4570650014006517498951317 214249219406555507763343)
  ·
    refine ⟨321373829109833261645015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214249219406555507763343 321373829109833261645015)
    ·
      refine ⟨482060743664749892467523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321373829109833261645015 482060743664749892467523)
      ·
        refine ⟨723091115497124838701285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482060743664749892467523 723091115497124838701285)
        ·
          refine ⟨135579584155710907256491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 723091115497124838701285 135579584155710907256491)
          ·
            refine ⟨203369376233566360884737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135579584155710907256491 203369376233566360884737)
            ·
              refine ⟨152527032175174770663553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203369376233566360884737 152527032175174770663553)
              ·
                refine ⟨114395274131381077997665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152527032175174770663553 114395274131381077997665)
                ·
                  refine ⟨85796455598535808498249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114395274131381077997665 85796455598535808498249)
                  ·
                    rfl

theorem cell20_187974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_187974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187974 prefixEnd_187974 := by exact prefixLift 187974
  have htrace : WordTrace (prefixWord ++ tailWord_187974) baseStart_187974 baseEnd_187974 := by
    simpa [prefixWord, tailWord_187974, baseEnd_187974] using wordTrace_append hprefix tailTrace_187974
  have hstable : (prefixWord ++ tailWord_187974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187974).length < 2 ^ (prefixWord ++ tailWord_187974).sum := by decide
  have hdescent : baseEnd_187974 < baseStart_187974 := by decide
  rcases family_descends (prefixWord ++ tailWord_187974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187996 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 3]
def baseStart_187996 : Nat := 118140960795 + 187996 * 2 ^ 59
def prefixEnd_187996 : Nat := 4983230072969 + 3 ^ 40 * 187996 * 2
def baseEnd_187996 : Nat := 85806496998001509764825

theorem tailTrace_187996 : CollatzResearch.WordTrace tailWord_187996 prefixEnd_187996 85806496998001509764825 := by
  unfold tailWord_187996
  simp only [CollatzResearch.WordTrace]
  refine ⟨3428388713465037002863921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4571184951286716003818561 3428388713465037002863921)
  ·
    refine ⟨2571291535098777752147941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3428388713465037002863921 2571291535098777752147941)
    ·
      refine ⟨482117162831020828527739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2571291535098777752147941 482117162831020828527739)
      ·
        refine ⟨723175744246531242791609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482117162831020828527739 723175744246531242791609)
        ·
          refine ⟨542381808184898432093707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723175744246531242791609 542381808184898432093707)
          ·
            refine ⟨813572712277347648140561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542381808184898432093707 813572712277347648140561)
            ·
              refine ⟨610179534208010736105421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813572712277347648140561 610179534208010736105421)
              ·
                refine ⟨228817325328004026039533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 610179534208010736105421 228817325328004026039533)
                ·
                  refine ⟨85806496998001509764825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228817325328004026039533 85806496998001509764825)
                  ·
                    rfl

theorem cell20_187996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_187996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_187996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_187996 prefixEnd_187996 := by exact prefixLift 187996
  have htrace : WordTrace (prefixWord ++ tailWord_187996) baseStart_187996 baseEnd_187996 := by
    simpa [prefixWord, tailWord_187996, baseEnd_187996] using wordTrace_append hprefix tailTrace_187996
  have hstable : (prefixWord ++ tailWord_187996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187996).length < 2 ^ (prefixWord ++ tailWord_187996).sum := by decide
  have hdescent : baseEnd_187996 < baseStart_187996 := by decide
  rcases family_descends (prefixWord ++ tailWord_187996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188000 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_188000 : Nat := 118140960795 + 188000 * 2 ^ 59
def prefixEnd_188000 : Nat := 4983230072969 + 3 ^ 40 * 188000 * 2
def baseEnd_188000 : Nat := 85808322706995273631475

theorem tailTrace_188000 : CollatzResearch.WordTrace tailWord_188000 prefixEnd_188000 85808322706995273631475 := by
  unfold tailWord_188000
  simp only [CollatzResearch.WordTrace]
  refine ⟨3428461659457791344436727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4571282212610388459248969 3428461659457791344436727)
  ·
    refine ⟨5142692489186687016655091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3428461659457791344436727 5142692489186687016655091)
    ·
      refine ⟨7714038733780030524982637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5142692489186687016655091 7714038733780030524982637)
      ·
        refine ⟨2892764525167511446868489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7714038733780030524982637 2892764525167511446868489)
        ·
          refine ⟨2169573393875633585151367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2892764525167511446868489 2169573393875633585151367)
          ·
            refine ⟨3254360090813450377727051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169573393875633585151367 3254360090813450377727051)
            ·
              refine ⟨4881540136220175566590577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254360090813450377727051 4881540136220175566590577)
              ·
                refine ⟨3661155102165131674942933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4881540136220175566590577 3661155102165131674942933)
                ·
                  refine ⟨85808322706995273631475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3661155102165131674942933 85808322706995273631475)
                  ·
                    rfl

theorem cell20_188000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_188000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188000 prefixEnd_188000 := by exact prefixLift 188000
  have htrace : WordTrace (prefixWord ++ tailWord_188000) baseStart_188000 baseEnd_188000 := by
    simpa [prefixWord, tailWord_188000, baseEnd_188000] using wordTrace_append hprefix tailTrace_188000
  have hstable : (prefixWord ++ tailWord_188000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188000).length < 2 ^ (prefixWord ++ tailWord_188000).sum := by decide
  have hdescent : baseEnd_188000 < baseStart_188000 := by decide
  rcases family_descends (prefixWord ++ tailWord_188000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188041 : List Nat := [1, 2, 1, 1, 4, 1, 4, 4, 2]
def baseStart_188041 : Nat := 118140960795 + 188041 * 2 ^ 59
def prefixEnd_188041 : Nat := 4983230072969 + 3 ^ 40 * 188041 * 2
def baseEnd_188041 : Nat := 85827036224181353264641

theorem tailTrace_188041 : CollatzResearch.WordTrace tailWord_188041 prefixEnd_188041 85827036224181353264641 := by
  unfold tailWord_188041
  simp only [CollatzResearch.WordTrace]
  refine ⟨6858418711767046691115977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4572279141178031127410651 6858418711767046691115977)
  ·
    refine ⟨5143814033825285018336983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6858418711767046691115977 5143814033825285018336983)
    ·
      refine ⟨7715721050737927527505475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5143814033825285018336983 7715721050737927527505475)
      ·
        refine ⟨11573581576106891291258213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7715721050737927527505475 11573581576106891291258213)
        ·
          refine ⟨2170046545520042117110915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11573581576106891291258213 2170046545520042117110915)
          ·
            refine ⟨3255069818280063175666373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170046545520042117110915 3255069818280063175666373)
            ·
              refine ⟨610325590927511845437445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3255069818280063175666373 610325590927511845437445)
              ·
                refine ⟨114436048298908471019521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 610325590927511845437445 114436048298908471019521)
                ·
                  refine ⟨85827036224181353264641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114436048298908471019521 85827036224181353264641)
                  ·
                    rfl

theorem cell20_188041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 2].length) (baseStart_188041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188041 prefixEnd_188041 := by exact prefixLift 188041
  have htrace : WordTrace (prefixWord ++ tailWord_188041) baseStart_188041 baseEnd_188041 := by
    simpa [prefixWord, tailWord_188041, baseEnd_188041] using wordTrace_append hprefix tailTrace_188041
  have hstable : (prefixWord ++ tailWord_188041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188041).length < 2 ^ (prefixWord ++ tailWord_188041).sum := by decide
  have hdescent : baseEnd_188041 < baseStart_188041 := by decide
  rcases family_descends (prefixWord ++ tailWord_188041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188065 : List Nat := [1, 2, 3, 3, 2, 3, 2, 4]
def baseStart_188065 : Nat := 118140960795 + 188065 * 2 ^ 59
def prefixEnd_188065 : Nat := 4983230072969 + 3 ^ 40 * 188065 * 2
def baseEnd_188065 : Nat := 28612663492714645488181

theorem tailTrace_188065 : CollatzResearch.WordTrace tailWord_188065 prefixEnd_188065 28612663492714645488181 := by
  unfold tailWord_188065
  simp only [CollatzResearch.WordTrace]
  refine ⟨6859294063680098789989649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4572862709120065859993099 6859294063680098789989649)
  ·
    refine ⟨5144470547760074092492237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6859294063680098789989649 5144470547760074092492237)
    ·
      refine ⟨1929176455410027784684589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5144470547760074092492237 1929176455410027784684589)
      ·
        refine ⟨723441170778760419256721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1929176455410027784684589 723441170778760419256721)
        ·
          refine ⟨542580878084070314442541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723441170778760419256721 542580878084070314442541)
          ·
            refine ⟨203467829281526367915953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 542580878084070314442541 203467829281526367915953)
            ·
              refine ⟨152600871961144775936965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203467829281526367915953 152600871961144775936965)
              ·
                refine ⟨28612663492714645488181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152600871961144775936965 28612663492714645488181)
                ·
                  rfl

theorem cell20_188065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 4].length) (baseStart_188065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188065 prefixEnd_188065 := by exact prefixLift 188065
  have htrace : WordTrace (prefixWord ++ tailWord_188065) baseStart_188065 baseEnd_188065 := by
    simpa [prefixWord, tailWord_188065, baseEnd_188065] using wordTrace_append hprefix tailTrace_188065
  have hstable : (prefixWord ++ tailWord_188065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188065).length < 2 ^ (prefixWord ++ tailWord_188065).sum := by decide
  have hdescent : baseEnd_188065 < baseStart_188065 := by decide
  rcases family_descends (prefixWord ++ tailWord_188065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188093 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 3]
def baseStart_188093 : Nat := 118140960795 + 188093 * 2 ^ 59
def prefixEnd_188093 : Nat := 4983230072969 + 3 ^ 40 * 188093 * 2
def baseEnd_188093 : Nat := 85850770441100283531095

theorem tailTrace_188093 : CollatzResearch.WordTrace tailWord_188093 prefixEnd_188093 85850770441100283531095 := by
  unfold tailWord_188093
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860315307578659572008933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4573543538385773048005955 6860315307578659572008933)
  ·
    refine ⟨1286309120170998669751675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6860315307578659572008933 1286309120170998669751675)
    ·
      refine ⟨1929463680256498004627513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286309120170998669751675 1929463680256498004627513)
      ·
        refine ⟨1447097760192373503470635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1929463680256498004627513 1447097760192373503470635)
        ·
          refine ⟨2170646640288560255205953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447097760192373503470635 2170646640288560255205953)
          ·
            refine ⟨1627984980216420191404465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2170646640288560255205953 1627984980216420191404465)
            ·
              refine ⟨1220988735162315143553349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1627984980216420191404465 1220988735162315143553349)
              ·
                refine ⟨228935387842934089416253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1220988735162315143553349 228935387842934089416253)
                ·
                  refine ⟨85850770441100283531095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228935387842934089416253 85850770441100283531095)
                  ·
                    rfl

theorem cell20_188093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_188093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188093 prefixEnd_188093 := by exact prefixLift 188093
  have htrace : WordTrace (prefixWord ++ tailWord_188093) baseStart_188093 baseEnd_188093 := by
    simpa [prefixWord, tailWord_188093, baseEnd_188093] using wordTrace_append hprefix tailTrace_188093
  have hstable : (prefixWord ++ tailWord_188093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188093).length < 2 ^ (prefixWord ++ tailWord_188093).sum := by decide
  have hdescent : baseEnd_188093 < baseStart_188093 := by decide
  rcases family_descends (prefixWord ++ tailWord_188093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188096 : List Nat := [2, 1, 1, 2, 4, 1, 5, 2, 2]
def baseStart_188096 : Nat := 118140960795 + 188096 * 2 ^ 59
def prefixEnd_188096 : Nat := 4983230072969 + 3 ^ 40 * 188096 * 2
def baseEnd_188096 : Nat := 85852139722845606431083

theorem tailTrace_188096 : CollatzResearch.WordTrace tailWord_188096 prefixEnd_188096 85852139722845606431083 := by
  unfold tailWord_188096
  simp only [CollatzResearch.WordTrace]
  refine ⟨3430212363283895542184071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4573616484378527389578761 3430212363283895542184071)
  ·
    refine ⟨5145318544925843313276107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3430212363283895542184071 5145318544925843313276107)
    ·
      refine ⟨7717977817388764969914161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5145318544925843313276107 7717977817388764969914161)
      ·
        refine ⟨5788483363041573727435621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7717977817388764969914161 5788483363041573727435621)
        ·
          refine ⟨1085340630570295073894179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5788483363041573727435621 1085340630570295073894179)
          ·
            refine ⟨1628010945855442610841269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085340630570295073894179 1628010945855442610841269)
            ·
              refine ⟨152626026173947744766369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1628010945855442610841269 152626026173947744766369)
              ·
                refine ⟨114469519630460808574777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152626026173947744766369 114469519630460808574777)
                ·
                  refine ⟨85852139722845606431083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114469519630460808574777 85852139722845606431083)
                  ·
                    rfl

theorem cell20_188096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 2].length) (baseStart_188096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188096 prefixEnd_188096 := by exact prefixLift 188096
  have htrace : WordTrace (prefixWord ++ tailWord_188096) baseStart_188096 baseEnd_188096 := by
    simpa [prefixWord, tailWord_188096, baseEnd_188096] using wordTrace_append hprefix tailTrace_188096
  have hstable : (prefixWord ++ tailWord_188096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188096).length < 2 ^ (prefixWord ++ tailWord_188096).sum := by decide
  have hdescent : baseEnd_188096 < baseStart_188096 := by decide
  rcases family_descends (prefixWord ++ tailWord_188096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188106 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 3]
def baseStart_188106 : Nat := 118140960795 + 188106 * 2 ^ 59
def prefixEnd_188106 : Nat := 4983230072969 + 3 ^ 40 * 188106 * 2
def baseEnd_188106 : Nat := 85856703995330016097709

theorem tailTrace_188106 : CollatzResearch.WordTrace tailWord_188106 prefixEnd_188106 85856703995330016097709 := by
  unfold tailWord_188106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1715197364132890698058043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4573859637687708528154781 1715197364132890698058043)
  ·
    refine ⟨2572796046199336047087065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1715197364132890698058043 2572796046199336047087065)
    ·
      refine ⟨1929597034649502035315299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2572796046199336047087065 1929597034649502035315299)
      ·
        refine ⟨2894395551974253052972949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929597034649502035315299 2894395551974253052972949)
        ·
          refine ⟨135674791498793111858107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2894395551974253052972949 135674791498793111858107)
          ·
            refine ⟨203512187248189667787161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135674791498793111858107 203512187248189667787161)
            ·
              refine ⟨152634140436142250840371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203512187248189667787161 152634140436142250840371)
              ·
                refine ⟨228951210654213376260557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152634140436142250840371 228951210654213376260557)
                ·
                  refine ⟨85856703995330016097709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228951210654213376260557 85856703995330016097709)
                  ·
                    rfl

theorem cell20_188106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_188106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188106 prefixEnd_188106 := by exact prefixLift 188106
  have htrace : WordTrace (prefixWord ++ tailWord_188106) baseStart_188106 baseEnd_188106 := by
    simpa [prefixWord, tailWord_188106, baseEnd_188106] using wordTrace_append hprefix tailTrace_188106
  have hstable : (prefixWord ++ tailWord_188106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188106).length < 2 ^ (prefixWord ++ tailWord_188106).sum := by decide
  have hdescent : baseEnd_188106 < baseStart_188106 := by decide
  rcases family_descends (prefixWord ++ tailWord_188106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188158 : List Nat := [4, 2, 2, 1, 4, 1, 1, 5]
def baseStart_188158 : Nat := 118140960795 + 188158 * 2 ^ 59
def prefixEnd_188158 : Nat := 4983230072969 + 3 ^ 40 * 188158 * 2
def baseEnd_188158 : Nat := 28626812737416315454721

theorem tailTrace_188158 : CollatzResearch.WordTrace tailWord_188158 prefixEnd_188158 28626812737416315454721 := by
  unfold tailWord_188158
  simp only [CollatzResearch.WordTrace]
  refine ⟨857835756542896959140641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4575124034895450448750085 857835756542896959140641)
  ·
    refine ⟨643376817407172719355481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 857835756542896959140641 643376817407172719355481)
    ·
      refine ⟨482532613055379539516611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 643376817407172719355481 482532613055379539516611)
      ·
        refine ⟨723798919583069309274917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482532613055379539516611 723798919583069309274917)
        ·
          refine ⟨135712297421825495489047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 723798919583069309274917 135712297421825495489047)
          ·
            refine ⟨203568446132738243233571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135712297421825495489047 203568446132738243233571)
            ·
              refine ⟨305352669199107364850357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203568446132738243233571 305352669199107364850357)
              ·
                refine ⟨28626812737416315454721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 305352669199107364850357 28626812737416315454721)
                ·
                  rfl

theorem cell20_188158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_188158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188158 prefixEnd_188158 := by exact prefixLift 188158
  have htrace : WordTrace (prefixWord ++ tailWord_188158) baseStart_188158 baseEnd_188158 := by
    simpa [prefixWord, tailWord_188158, baseEnd_188158] using wordTrace_append hprefix tailTrace_188158
  have hstable : (prefixWord ++ tailWord_188158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188158).length < 2 ^ (prefixWord ++ tailWord_188158).sum := by decide
  have hdescent : baseEnd_188158 < baseStart_188158 := by decide
  rcases family_descends (prefixWord ++ tailWord_188158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188193 : List Nat := [1, 2, 3, 2, 1, 3, 1, 5, 2]
def baseStart_188193 : Nat := 118140960795 + 188193 * 2 ^ 59
def prefixEnd_188193 : Nat := 4983230072969 + 3 ^ 40 * 188193 * 2
def baseEnd_188193 : Nat := 85896413165944380197353

theorem tailTrace_188193 : CollatzResearch.WordTrace tailWord_188193 prefixEnd_188193 85896413165944380197353 := by
  unfold tailWord_188193
  simp only [CollatzResearch.WordTrace]
  refine ⟨6863962607216376650649233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4575975071477584433766155 6863962607216376650649233)
  ·
    refine ⟨5147971955412282487986925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6863962607216376650649233 5147971955412282487986925)
    ·
      refine ⟨1930489483279605932995097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5147971955412282487986925 1930489483279605932995097)
      ·
        refine ⟨1447867112459704449746323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1930489483279605932995097 1447867112459704449746323)
        ·
          refine ⟨2171800668689556674619485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447867112459704449746323 2171800668689556674619485)
          ·
            refine ⟨814425250758583752982307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2171800668689556674619485 814425250758583752982307)
            ·
              refine ⟨1221637876137875629473461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814425250758583752982307 1221637876137875629473461)
              ·
                refine ⟨114528550887925840263137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1221637876137875629473461 114528550887925840263137)
                ·
                  refine ⟨85896413165944380197353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114528550887925840263137 85896413165944380197353)
                  ·
                    rfl

theorem cell20_188193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 2].length) (baseStart_188193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188193 prefixEnd_188193 := by exact prefixLift 188193
  have htrace : WordTrace (prefixWord ++ tailWord_188193) baseStart_188193 baseEnd_188193 := by
    simpa [prefixWord, tailWord_188193, baseEnd_188193] using wordTrace_append hprefix tailTrace_188193
  have hstable : (prefixWord ++ tailWord_188193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188193).length < 2 ^ (prefixWord ++ tailWord_188193).sum := by decide
  have hdescent : baseEnd_188193 < baseStart_188193 := by decide
  rcases family_descends (prefixWord ++ tailWord_188193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188269 : List Nat := [1, 5, 1, 1, 1, 1, 2, 6, 2]
def baseStart_188269 : Nat := 118140960795 + 188269 * 2 ^ 59
def prefixEnd_188269 : Nat := 4983230072969 + 3 ^ 40 * 188269 * 2
def baseEnd_188269 : Nat := 85931101636825893663709

theorem tailTrace_188269 : CollatzResearch.WordTrace tailWord_188269 prefixEnd_188269 85931101636825893663709 := by
  unfold tailWord_188269
  simp only [CollatzResearch.WordTrace]
  refine ⟨6866734554941041630415861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4577823036627361086943907 6866734554941041630415861)
  ·
    refine ⟨643756364525722652851487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6866734554941041630415861 643756364525722652851487)
    ·
      refine ⟨965634546788583979277231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643756364525722652851487 965634546788583979277231)
      ·
        refine ⟨1448451820182875968915847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965634546788583979277231 1448451820182875968915847)
        ·
          refine ⟨2172677730274313953373771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448451820182875968915847 2172677730274313953373771)
          ·
            refine ⟨3259016595411470930060657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172677730274313953373771 3259016595411470930060657)
            ·
              refine ⟨2444262446558603197545493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3259016595411470930060657 2444262446558603197545493)
              ·
                refine ⟨114574802182434524884945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2444262446558603197545493 114574802182434524884945)
                ·
                  refine ⟨85931101636825893663709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114574802182434524884945 85931101636825893663709)
                  ·
                    rfl

theorem cell20_188269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_188269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188269 prefixEnd_188269 := by exact prefixLift 188269
  have htrace : WordTrace (prefixWord ++ tailWord_188269) baseStart_188269 baseEnd_188269 := by
    simpa [prefixWord, tailWord_188269, baseEnd_188269] using wordTrace_append hprefix tailTrace_188269
  have hstable : (prefixWord ++ tailWord_188269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188269).length < 2 ^ (prefixWord ++ tailWord_188269).sum := by decide
  have hdescent : baseEnd_188269 < baseStart_188269 := by decide
  rcases family_descends (prefixWord ++ tailWord_188269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188310 : List Nat := [5, 3, 1, 1, 3, 7]
def baseStart_188310 : Nat := 118140960795 + 188310 * 2 ^ 59
def prefixEnd_188310 : Nat := 4983230072969 + 3 ^ 40 * 188310 * 2
def baseEnd_188310 : Nat := 3183326487185628640625

theorem tailTrace_188310 : CollatzResearch.WordTrace tailWord_188310 prefixEnd_188310 3183326487185628640625 := by
  unfold tailWord_188310
  simp only [CollatzResearch.WordTrace]
  refine ⟨429264371737031602041149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4578819965195003755105589 429264371737031602041149)
  ·
    refine ⟨160974139401386850765431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 429264371737031602041149 160974139401386850765431)
    ·
      refine ⟨241461209102080276148147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160974139401386850765431 241461209102080276148147)
      ·
        refine ⟨362191813653120414222221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241461209102080276148147 362191813653120414222221)
        ·
          refine ⟨135821930119920155333333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362191813653120414222221 135821930119920155333333)
          ·
            refine ⟨3183326487185628640625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 135821930119920155333333 3183326487185628640625)
            ·
              rfl

theorem cell20_188310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 7].length) (baseStart_188310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188310 prefixEnd_188310 := by exact prefixLift 188310
  have htrace : WordTrace (prefixWord ++ tailWord_188310) baseStart_188310 baseEnd_188310 := by
    simpa [prefixWord, tailWord_188310, baseEnd_188310] using wordTrace_append hprefix tailTrace_188310
  have hstable : (prefixWord ++ tailWord_188310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188310).length < 2 ^ (prefixWord ++ tailWord_188310).sum := by decide
  have hdescent : baseEnd_188310 < baseStart_188310 := by decide
  rcases family_descends (prefixWord ++ tailWord_188310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188324 : List Nat := [2, 3, 1, 2, 1, 3, 4, 2, 2]
def baseStart_188324 : Nat := 118140960795 + 188324 * 2 ^ 59
def prefixEnd_188324 : Nat := 4983230072969 + 3 ^ 40 * 188324 * 2
def baseEnd_188324 : Nat := 85956205135490146830151

theorem tailTrace_188324 : CollatzResearch.WordTrace tailWord_188324 prefixEnd_188324 85956205135490146830151 := by
  unfold tailWord_188324
  simp only [CollatzResearch.WordTrace]
  refine ⟨3434370284870893011834013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4579160379827857349112017 3434370284870893011834013)
  ·
    refine ⟨1287888856826584879437755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3434370284870893011834013 1287888856826584879437755)
    ·
      refine ⟨1931833285239877319156633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1287888856826584879437755 1931833285239877319156633)
      ·
        refine ⟨1448874963929907989367475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1931833285239877319156633 1448874963929907989367475)
        ·
          refine ⟨2173312445894861984051213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448874963929907989367475 2173312445894861984051213)
          ·
            refine ⟨814992167210573244019205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2173312445894861984051213 814992167210573244019205)
            ·
              refine ⟨152811031351982483253601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 814992167210573244019205 152811031351982483253601)
              ·
                refine ⟨114608273513986862440201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152811031351982483253601 114608273513986862440201)
                ·
                  refine ⟨85956205135490146830151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114608273513986862440201 85956205135490146830151)
                  ·
                    rfl

theorem cell20_188324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_188324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188324 prefixEnd_188324 := by exact prefixLift 188324
  have htrace : WordTrace (prefixWord ++ tailWord_188324) baseStart_188324 baseEnd_188324 := by
    simpa [prefixWord, tailWord_188324, baseEnd_188324] using wordTrace_append hprefix tailTrace_188324
  have hstable : (prefixWord ++ tailWord_188324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188324).length < 2 ^ (prefixWord ++ tailWord_188324).sum := by decide
  have hdescent : baseEnd_188324 < baseStart_188324 := by decide
  rcases family_descends (prefixWord ++ tailWord_188324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188373 : List Nat := [1, 3, 2, 3, 2, 2, 7]
def baseStart_188373 : Nat := 118140960795 + 188373 * 2 ^ 59
def prefixEnd_188373 : Nat := 4983230072969 + 3 ^ 40 * 188373 * 2
def baseEnd_188373 : Nat := 9553174452295972688513

theorem tailTrace_188373 : CollatzResearch.WordTrace tailWord_188373 prefixEnd_188373 9553174452295972688513 := by
  unfold tailWord_188373
  simp only [CollatzResearch.WordTrace]
  refine ⟨6870527746564267392201773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4580351831042844928134515 6870527746564267392201773)
  ·
    refine ⟨2576447904961600272075665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6870527746564267392201773 2576447904961600272075665)
    ·
      refine ⟨1932335928721200204056749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2576447904961600272075665 1932335928721200204056749)
      ·
        refine ⟨724625973270450076521281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1932335928721200204056749 724625973270450076521281)
        ·
          refine ⟨543469479952837557390961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724625973270450076521281 543469479952837557390961)
          ·
            refine ⟨407602109964628168043221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543469479952837557390961 407602109964628168043221)
            ·
              refine ⟨9553174452295972688513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 407602109964628168043221 9553174452295972688513)
              ·
                rfl

theorem cell20_188373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 7].length) (baseStart_188373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188373 prefixEnd_188373 := by exact prefixLift 188373
  have htrace : WordTrace (prefixWord ++ tailWord_188373) baseStart_188373 baseEnd_188373 := by
    simpa [prefixWord, tailWord_188373, baseEnd_188373] using wordTrace_append hprefix tailTrace_188373
  have hstable : (prefixWord ++ tailWord_188373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188373).length < 2 ^ (prefixWord ++ tailWord_188373).sum := by decide
  have hdescent : baseEnd_188373 < baseStart_188373 := by decide
  rcases family_descends (prefixWord ++ tailWord_188373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188383 : List Nat := [1, 1, 2, 3, 4, 1, 2, 4, 2]
def baseStart_188383 : Nat := 118140960795 + 188383 * 2 ^ 59
def prefixEnd_188383 : Nat := 4983230072969 + 3 ^ 40 * 188383 * 2
def baseEnd_188383 : Nat := 85983134343148163863243

theorem tailTrace_188383 : CollatzResearch.WordTrace tailWord_188383 prefixEnd_188383 85983134343148163863243 := by
  unfold tailWord_188383
  simp only [CollatzResearch.WordTrace]
  refine ⟨6870892476528039100065803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4580594984352026066710535 6870892476528039100065803)
  ·
    refine ⟨10306338714792058650098705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6870892476528039100065803 10306338714792058650098705)
    ·
      refine ⟨7729754036094043987574029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10306338714792058650098705 7729754036094043987574029)
      ·
        refine ⟨2898657763535266495340261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7729754036094043987574029 2898657763535266495340261)
        ·
          refine ⟨543498330662862467876299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2898657763535266495340261 543498330662862467876299)
          ·
            refine ⟨815247495994293701814449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543498330662862467876299 815247495994293701814449)
            ·
              refine ⟨611435621995720276360837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815247495994293701814449 611435621995720276360837)
              ·
                refine ⟨114644179124197551817657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 611435621995720276360837 114644179124197551817657)
                ·
                  refine ⟨85983134343148163863243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114644179124197551817657 85983134343148163863243)
                  ·
                    rfl

theorem cell20_188383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 2].length) (baseStart_188383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188383 prefixEnd_188383 := by exact prefixLift 188383
  have htrace : WordTrace (prefixWord ++ tailWord_188383) baseStart_188383 baseEnd_188383 := by
    simpa [prefixWord, tailWord_188383, baseEnd_188383] using wordTrace_append hprefix tailTrace_188383
  have hstable : (prefixWord ++ tailWord_188383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188383).length < 2 ^ (prefixWord ++ tailWord_188383).sum := by decide
  have hdescent : baseEnd_188383 < baseStart_188383 := by decide
  rcases family_descends (prefixWord ++ tailWord_188383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188411 : List Nat := [1, 1, 1, 1, 1, 3, 8, 4]
def baseStart_188411 : Nat := 118140960795 + 188411 * 2 ^ 59
def prefixEnd_188411 : Nat := 4983230072969 + 3 ^ 40 * 188411 * 2
def baseEnd_188411 : Nat := 28665304768701503643265

theorem tailTrace_188411 : CollatzResearch.WordTrace tailWord_188411 prefixEnd_188411 28665304768701503643265 := by
  unfold tailWord_188411
  simp only [CollatzResearch.WordTrace]
  refine ⟨6871913720426599882085087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4581275813617733254723391 6871913720426599882085087)
  ·
    refine ⟨10307870580639899823127631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6871913720426599882085087 10307870580639899823127631)
    ·
      refine ⟨15461805870959849734691447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10307870580639899823127631 15461805870959849734691447)
      ·
        refine ⟨23192708806439774602037171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15461805870959849734691447 23192708806439774602037171)
        ·
          refine ⟨34789063209659661903055757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23192708806439774602037171 34789063209659661903055757)
          ·
            refine ⟨13045898703622373213645909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34789063209659661903055757 13045898703622373213645909)
            ·
              refine ⟨152881625433074686097413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 13045898703622373213645909 152881625433074686097413)
              ·
                refine ⟨28665304768701503643265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152881625433074686097413 28665304768701503643265)
                ·
                  rfl

theorem cell20_188411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 4].length) (baseStart_188411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188411 prefixEnd_188411 := by exact prefixLift 188411
  have htrace : WordTrace (prefixWord ++ tailWord_188411) baseStart_188411 baseEnd_188411 := by
    simpa [prefixWord, tailWord_188411, baseEnd_188411] using wordTrace_append hprefix tailTrace_188411
  have hstable : (prefixWord ++ tailWord_188411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188411).length < 2 ^ (prefixWord ++ tailWord_188411).sum := by decide
  have hdescent : baseEnd_188411 < baseStart_188411 := by decide
  rcases family_descends (prefixWord ++ tailWord_188411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188421 : List Nat := [1, 3, 1, 1, 2, 4, 3, 3, 2]
def baseStart_188421 : Nat := 118140960795 + 188421 * 2 ^ 59
def prefixEnd_188421 : Nat := 4983230072969 + 3 ^ 40 * 188421 * 2
def baseEnd_188421 : Nat := 86000478578588920596421

theorem tailTrace_188421 : CollatzResearch.WordTrace tailWord_188421 prefixEnd_188421 86000478578588920596421 := by
  unfold tailWord_188421
  simp only [CollatzResearch.WordTrace]
  refine ⟨6872278450390371589949117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4581518966926914393299411 6872278450390371589949117)
  ·
    refine ⟨2577104418896389346230919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6872278450390371589949117 2577104418896389346230919)
    ·
      refine ⟨3865656628344584019346379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2577104418896389346230919 3865656628344584019346379)
      ·
        refine ⟨5798484942516876029019569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3865656628344584019346379 5798484942516876029019569)
        ·
          refine ⟨4348863706887657021764677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5798484942516876029019569 4348863706887657021764677)
          ·
            refine ⟨815411945041435691580877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4348863706887657021764677 815411945041435691580877)
            ·
              refine ⟨305779479390538384342829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 815411945041435691580877 305779479390538384342829)
              ·
                refine ⟨114667304771451894128561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305779479390538384342829 114667304771451894128561)
                ·
                  refine ⟨86000478578588920596421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114667304771451894128561 86000478578588920596421)
                  ·
                    rfl

theorem cell20_188421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_188421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188421 prefixEnd_188421 := by exact prefixLift 188421
  have htrace : WordTrace (prefixWord ++ tailWord_188421) baseStart_188421 baseEnd_188421 := by
    simpa [prefixWord, tailWord_188421, baseEnd_188421] using wordTrace_append hprefix tailTrace_188421
  have hstable : (prefixWord ++ tailWord_188421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188421).length < 2 ^ (prefixWord ++ tailWord_188421).sum := by decide
  have hdescent : baseEnd_188421 < baseStart_188421 := by decide
  rcases family_descends (prefixWord ++ tailWord_188421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188442 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_188442 : Nat := 118140960795 + 188442 * 2 ^ 59
def prefixEnd_188442 : Nat := 4983230072969 + 3 ^ 40 * 188442 * 2
def baseEnd_188442 : Nat := 86010063550806180896335

theorem tailTrace_188442 : CollatzResearch.WordTrace tailWord_188442 prefixEnd_188442 86010063550806180896335 := by
  unfold tailWord_188442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1718261095828573044115895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4582029588876194784309053 1718261095828573044115895)
  ·
    refine ⟨2577391643742859566173843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1718261095828573044115895 2577391643742859566173843)
    ·
      refine ⟨3866087465614289349260765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2577391643742859566173843 3866087465614289349260765)
      ·
        refine ⟨1449782799605358505972787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3866087465614289349260765 1449782799605358505972787)
        ·
          refine ⟨2174674199408037758959181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1449782799605358505972787 2174674199408037758959181)
          ·
            refine ⟨815502824778014159609693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2174674199408037758959181 815502824778014159609693)
            ·
              refine ⟨305813559291755309853635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 815502824778014159609693 305813559291755309853635)
              ·
                refine ⟨458720338937632964780453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305813559291755309853635 458720338937632964780453)
                ·
                  refine ⟨86010063550806180896335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 458720338937632964780453 86010063550806180896335)
                  ·
                    rfl

theorem cell20_188442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_188442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188442 prefixEnd_188442 := by exact prefixLift 188442
  have htrace : WordTrace (prefixWord ++ tailWord_188442) baseStart_188442 baseEnd_188442 := by
    simpa [prefixWord, tailWord_188442, baseEnd_188442] using wordTrace_append hprefix tailTrace_188442
  have hstable : (prefixWord ++ tailWord_188442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188442).length < 2 ^ (prefixWord ++ tailWord_188442).sum := by decide
  have hdescent : baseEnd_188442 < baseStart_188442 := by decide
  rcases family_descends (prefixWord ++ tailWord_188442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188452 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 3]
def baseStart_188452 : Nat := 118140960795 + 188452 * 2 ^ 59
def prefixEnd_188452 : Nat := 4983230072969 + 3 ^ 40 * 188452 * 2
def baseEnd_188452 : Nat := 86014627823290590562961

theorem tailTrace_188452 : CollatzResearch.WordTrace tailWord_188452 prefixEnd_188452 86014627823290590562961 := by
  unfold tailWord_188452
  simp only [CollatzResearch.WordTrace]
  refine ⟨3436704556639031942163805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4582272742185375922885073 3436704556639031942163805)
  ·
    refine ⟨1288764208739636978311427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3436704556639031942163805 1288764208739636978311427)
    ·
      refine ⟨1933146313109455467467141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1288764208739636978311427 1933146313109455467467141)
      ·
        refine ⟨362464933708022900150089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1933146313109455467467141 362464933708022900150089)
        ·
          refine ⟨271848700281017175112567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362464933708022900150089 271848700281017175112567)
          ·
            refine ⟨407773050421525762668851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271848700281017175112567 407773050421525762668851)
            ·
              refine ⟨611659575632288644003277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407773050421525762668851 611659575632288644003277)
              ·
                refine ⟨229372340862108241501229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 611659575632288644003277 229372340862108241501229)
                ·
                  refine ⟨86014627823290590562961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229372340862108241501229 86014627823290590562961)
                  ·
                    rfl

theorem cell20_188452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_188452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188452 prefixEnd_188452 := by exact prefixLift 188452
  have htrace : WordTrace (prefixWord ++ tailWord_188452) baseStart_188452 baseEnd_188452 := by
    simpa [prefixWord, tailWord_188452, baseEnd_188452] using wordTrace_append hprefix tailTrace_188452
  have hstable : (prefixWord ++ tailWord_188452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188452).length < 2 ^ (prefixWord ++ tailWord_188452).sum := by decide
  have hdescent : baseEnd_188452 < baseStart_188452 := by decide
  rcases family_descends (prefixWord ++ tailWord_188452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188535 : List Nat := [1, 1, 3, 1, 1, 6, 2, 3, 2]
def baseStart_188535 : Nat := 118140960795 + 188535 * 2 ^ 59
def prefixEnd_188535 : Nat := 4983230072969 + 3 ^ 40 * 188535 * 2
def baseEnd_188535 : Nat := 86052511284911190795955

theorem tailTrace_188535 : CollatzResearch.WordTrace tailWord_188535 prefixEnd_188535 86052511284911190795955 := by
  unfold tailWord_188535
  simp only [CollatzResearch.WordTrace]
  refine ⟨6876436371977369059599059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4584290914651579373066039 6876436371977369059599059)
  ·
    refine ⟨10314654557966053589398589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6876436371977369059599059 10314654557966053589398589)
    ·
      refine ⟨3867995459237270096024471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10314654557966053589398589 3867995459237270096024471)
      ·
        refine ⟨5801993188855905144036707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3867995459237270096024471 5801993188855905144036707)
        ·
          refine ⟨8702989783283857716055061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5801993188855905144036707 8702989783283857716055061)
          ·
            refine ⟨407952646091430830440081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8702989783283857716055061 407952646091430830440081)
            ·
              refine ⟨305964484568573122830061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407952646091430830440081 305964484568573122830061)
              ·
                refine ⟨114736681713214921061273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305964484568573122830061 114736681713214921061273)
                ·
                  refine ⟨86052511284911190795955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114736681713214921061273 86052511284911190795955)
                  ·
                    rfl

theorem cell20_188535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 2].length) (baseStart_188535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188535 prefixEnd_188535 := by exact prefixLift 188535
  have htrace : WordTrace (prefixWord ++ tailWord_188535) baseStart_188535 baseEnd_188535 := by
    simpa [prefixWord, tailWord_188535, baseEnd_188535] using wordTrace_append hprefix tailTrace_188535
  have hstable : (prefixWord ++ tailWord_188535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188535).length < 2 ^ (prefixWord ++ tailWord_188535).sum := by decide
  have hdescent : baseEnd_188535 < baseStart_188535 := by decide
  rcases family_descends (prefixWord ++ tailWord_188535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188545 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 3]
def baseStart_188545 : Nat := 118140960795 + 188545 * 2 ^ 59
def prefixEnd_188545 : Nat := 4983230072969 + 3 ^ 40 * 188545 * 2
def baseEnd_188545 : Nat := 86057075557395600462581

theorem tailTrace_188545 : CollatzResearch.WordTrace tailWord_188545 prefixEnd_188545 86057075557395600462581 := by
  unfold tailWord_188545
  simp only [CollatzResearch.WordTrace]
  refine ⟨6876801101941140767463089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4584534067960760511642059 6876801101941140767463089)
  ·
    refine ⟨5157600826455855575597317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6876801101941140767463089 5157600826455855575597317)
    ·
      refine ⟨967050154960472920424497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5157600826455855575597317 967050154960472920424497)
      ·
        refine ⟨725287616220354690318373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 967050154960472920424497 725287616220354690318373)
        ·
          refine ⟨135991428041316504434695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 725287616220354690318373 135991428041316504434695)
          ·
            refine ⟨203987142061974756652043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135991428041316504434695 203987142061974756652043)
            ·
              refine ⟨305980713092962134978065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203987142061974756652043 305980713092962134978065)
              ·
                refine ⟨229485534819721601233549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305980713092962134978065 229485534819721601233549)
                ·
                  refine ⟨86057075557395600462581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229485534819721601233549 86057075557395600462581)
                  ·
                    rfl

theorem cell20_188545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 3].length) (baseStart_188545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188545 prefixEnd_188545 := by exact prefixLift 188545
  have htrace : WordTrace (prefixWord ++ tailWord_188545) baseStart_188545 baseEnd_188545 := by
    simpa [prefixWord, tailWord_188545, baseEnd_188545] using wordTrace_append hprefix tailTrace_188545
  have hstable : (prefixWord ++ tailWord_188545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188545).length < 2 ^ (prefixWord ++ tailWord_188545).sum := by decide
  have hdescent : baseEnd_188545 < baseStart_188545 := by decide
  rcases family_descends (prefixWord ++ tailWord_188545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188549 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 3]
def baseStart_188549 : Nat := 118140960795 + 188549 * 2 ^ 59
def prefixEnd_188549 : Nat := 4983230072969 + 3 ^ 40 * 188549 * 2
def baseEnd_188549 : Nat := 86058901266389364329231

theorem tailTrace_188549 : CollatzResearch.WordTrace tailWord_188549 prefixEnd_188549 86058901266389364329231 := by
  unfold tailWord_188549
  simp only [CollatzResearch.WordTrace]
  refine ⟨6876946993926649450608701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4584631329284432967072467 6876946993926649450608701)
  ·
    refine ⟨2578855122722493543978263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6876946993926649450608701 2578855122722493543978263)
    ·
      refine ⟨3868282684083740315967395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2578855122722493543978263 3868282684083740315967395)
      ·
        refine ⟨5802424026125610473951093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868282684083740315967395 5802424026125610473951093)
        ·
          refine ⟨543977252449275981932915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5802424026125610473951093 543977252449275981932915)
          ·
            refine ⟨815965878673913972899373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543977252449275981932915 815965878673913972899373)
            ·
              refine ⟨305987204502717739837265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 815965878673913972899373 305987204502717739837265)
              ·
                refine ⟨229490403377038304877949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305987204502717739837265 229490403377038304877949)
                ·
                  refine ⟨86058901266389364329231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229490403377038304877949 86058901266389364329231)
                  ·
                    rfl

theorem cell20_188549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_188549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188549 prefixEnd_188549 := by exact prefixLift 188549
  have htrace : WordTrace (prefixWord ++ tailWord_188549) baseStart_188549 baseEnd_188549 := by
    simpa [prefixWord, tailWord_188549, baseEnd_188549] using wordTrace_append hprefix tailTrace_188549
  have hstable : (prefixWord ++ tailWord_188549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188549).length < 2 ^ (prefixWord ++ tailWord_188549).sum := by decide
  have hdescent : baseEnd_188549 < baseStart_188549 := by decide
  rcases family_descends (prefixWord ++ tailWord_188549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188586 : List Nat := [3, 1, 5, 1, 3, 1, 1, 3, 2]
def baseStart_188586 : Nat := 118140960795 + 188586 * 2 ^ 59
def prefixEnd_188586 : Nat := 4983230072969 + 3 ^ 40 * 188586 * 2
def baseEnd_188586 : Nat := 86075789074581680095747

theorem tailTrace_188586 : CollatzResearch.WordTrace tailWord_188586 prefixEnd_188586 86075789074581680095747 := by
  unfold tailWord_188586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719574123698151192426403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4585530996528403179803741 1719574123698151192426403)
  ·
    refine ⟨2579361185547226788639605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1719574123698151192426403 2579361185547226788639605)
    ·
      refine ⟨241815111145052511434963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2579361185547226788639605 241815111145052511434963)
      ·
        refine ⟨362722666717578767152445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241815111145052511434963 362722666717578767152445)
        ·
          refine ⟨136021000019092037682167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362722666717578767152445 136021000019092037682167)
          ·
            refine ⟨204031500028638056523251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136021000019092037682167 204031500028638056523251)
            ·
              refine ⟨306047250042957084784877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204031500028638056523251 306047250042957084784877)
              ·
                refine ⟨114767718766108906794329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306047250042957084784877 114767718766108906794329)
                ·
                  refine ⟨86075789074581680095747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114767718766108906794329 86075789074581680095747)
                  ·
                    rfl

theorem cell20_188586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_188586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188586 prefixEnd_188586 := by exact prefixLift 188586
  have htrace : WordTrace (prefixWord ++ tailWord_188586) baseStart_188586 baseEnd_188586 := by
    simpa [prefixWord, tailWord_188586, baseEnd_188586] using wordTrace_append hprefix tailTrace_188586
  have hstable : (prefixWord ++ tailWord_188586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188586).length < 2 ^ (prefixWord ++ tailWord_188586).sum := by decide
  have hdescent : baseEnd_188586 < baseStart_188586 := by decide
  rcases family_descends (prefixWord ++ tailWord_188586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188597 : List Nat := [1, 3, 3, 4, 2, 1, 6]
def baseStart_188597 : Nat := 118140960795 + 188597 * 2 ^ 59
def prefixEnd_188597 : Nat := 4983230072969 + 3 ^ 40 * 188597 * 2
def baseEnd_188597 : Nat := 9564534419368281192115

theorem tailTrace_188597 : CollatzResearch.WordTrace tailWord_188597 prefixEnd_188597 9564534419368281192115 := by
  unfold tailWord_188597
  simp only [CollatzResearch.WordTrace]
  refine ⟨6878697697752753648356045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4585798465168502432237363 6878697697752753648356045)
  ·
    refine ⟨2579511636657282618133517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6878697697752753648356045 2579511636657282618133517)
    ·
      refine ⟨967316863746480981800069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2579511636657282618133517 967316863746480981800069)
      ·
        refine ⟨181371911952465184087513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 967316863746480981800069 181371911952465184087513)
        ·
          refine ⟨136028933964348888065635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181371911952465184087513 136028933964348888065635)
          ·
            refine ⟨204043400946523332098453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136028933964348888065635 204043400946523332098453)
            ·
              refine ⟨9564534419368281192115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 204043400946523332098453 9564534419368281192115)
              ·
                rfl

theorem cell20_188597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 6].length) (baseStart_188597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188597 prefixEnd_188597 := by exact prefixLift 188597
  have htrace : WordTrace (prefixWord ++ tailWord_188597) baseStart_188597 baseEnd_188597 := by
    simpa [prefixWord, tailWord_188597, baseEnd_188597] using wordTrace_append hprefix tailTrace_188597
  have hstable : (prefixWord ++ tailWord_188597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188597).length < 2 ^ (prefixWord ++ tailWord_188597).sum := by decide
  have hdescent : baseEnd_188597 < baseStart_188597 := by decide
  rcases family_descends (prefixWord ++ tailWord_188597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188608 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_188608 : Nat := 118140960795 + 188608 * 2 ^ 59
def prefixEnd_188608 : Nat := 4983230072969 + 3 ^ 40 * 188608 * 2
def baseEnd_188608 : Nat := 86085830474047381362323

theorem tailTrace_188608 : CollatzResearch.WordTrace tailWord_188608 prefixEnd_188608 86085830474047381362323 := by
  unfold tailWord_188608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3439549450356451263503239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4586065933808601684670985 3439549450356451263503239)
  ·
    refine ⟨5159324175534676895254859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3439549450356451263503239 5159324175534676895254859)
    ·
      refine ⟨7738986263302015342882289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5159324175534676895254859 7738986263302015342882289)
      ·
        refine ⟨5804239697476511507161717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7738986263302015342882289 5804239697476511507161717)
        ·
          refine ⟨544147471638422953796411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5804239697476511507161717 544147471638422953796411)
          ·
            refine ⟨816221207457634430694617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544147471638422953796411 816221207457634430694617)
            ·
              refine ⟨612165905593225823020963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816221207457634430694617 612165905593225823020963)
              ·
                refine ⟨918248858389838734531445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612165905593225823020963 918248858389838734531445)
                ·
                  refine ⟨86085830474047381362323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 918248858389838734531445 86085830474047381362323)
                  ·
                    rfl

theorem cell20_188608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_188608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188608 prefixEnd_188608 := by exact prefixLift 188608
  have htrace : WordTrace (prefixWord ++ tailWord_188608) baseStart_188608 baseEnd_188608 := by
    simpa [prefixWord, tailWord_188608, baseEnd_188608] using wordTrace_append hprefix tailTrace_188608
  have hstable : (prefixWord ++ tailWord_188608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188608).length < 2 ^ (prefixWord ++ tailWord_188608).sum := by decide
  have hdescent : baseEnd_188608 < baseStart_188608 := by decide
  rcases family_descends (prefixWord ++ tailWord_188608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188625 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 3]
def baseStart_188625 : Nat := 118140960795 + 188625 * 2 ^ 59
def prefixEnd_188625 : Nat := 4983230072969 + 3 ^ 40 * 188625 * 2
def baseEnd_188625 : Nat := 86093589737270877795587

theorem tailTrace_188625 : CollatzResearch.WordTrace tailWord_188625 prefixEnd_188625 86093589737270877795587 := by
  unfold tailWord_188625
  simp only [CollatzResearch.WordTrace]
  refine ⟨6879718941651314430375329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4586479294434209620250219 6879718941651314430375329)
  ·
    refine ⟨5159789206238485822781497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6879718941651314430375329 5159789206238485822781497)
    ·
      refine ⟨3869841904678864367086123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5159789206238485822781497 3869841904678864367086123)
      ·
        refine ⟨5804762857018296550629185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3869841904678864367086123 5804762857018296550629185)
        ·
          refine ⟨4353572142763722412971889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5804762857018296550629185 4353572142763722412971889)
          ·
            refine ⟨3265179107072791809728917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4353572142763722412971889 3265179107072791809728917)
            ·
              refine ⟨153055270644037116081043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3265179107072791809728917 153055270644037116081043)
              ·
                refine ⟨229582905966055674121565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153055270644037116081043 229582905966055674121565)
                ·
                  refine ⟨86093589737270877795587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229582905966055674121565 86093589737270877795587)
                  ·
                    rfl

theorem cell20_188625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_188625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188625 prefixEnd_188625 := by exact prefixLift 188625
  have htrace : WordTrace (prefixWord ++ tailWord_188625) baseStart_188625 baseEnd_188625 := by
    simpa [prefixWord, tailWord_188625, baseEnd_188625] using wordTrace_append hprefix tailTrace_188625
  have hstable : (prefixWord ++ tailWord_188625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188625).length < 2 ^ (prefixWord ++ tailWord_188625).sum := by decide
  have hdescent : baseEnd_188625 < baseStart_188625 := by decide
  rcases family_descends (prefixWord ++ tailWord_188625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188666 : List Nat := [3, 1, 1, 1, 1, 7, 2, 2, 2]
def baseStart_188666 : Nat := 118140960795 + 188666 * 2 ^ 59
def prefixEnd_188666 : Nat := 4983230072969 + 3 ^ 40 * 188666 * 2
def baseEnd_188666 : Nat := 86112303254456957428753

theorem tailTrace_188666 : CollatzResearch.WordTrace tailWord_188666 prefixEnd_188666 86112303254456957428753 := by
  unfold tailWord_188666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1720303583625694608154463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4587476223001852288411901 1720303583625694608154463)
  ·
    refine ⟨2580455375438541912231695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1720303583625694608154463 2580455375438541912231695)
    ·
      refine ⟨3870683063157812868347543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580455375438541912231695 3870683063157812868347543)
      ·
        refine ⟨5806024594736719302521315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3870683063157812868347543 5806024594736719302521315)
        ·
          refine ⟨8709036892105078953781973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5806024594736719302521315 8709036892105078953781973)
          ·
            refine ⟨204118052158712787979265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 8709036892105078953781973 204118052158712787979265)
            ·
              refine ⟨153088539119034590984449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204118052158712787979265 153088539119034590984449)
              ·
                refine ⟨114816404339275943238337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153088539119034590984449 114816404339275943238337)
                ·
                  refine ⟨86112303254456957428753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114816404339275943238337 86112303254456957428753)
                  ·
                    rfl

theorem cell20_188666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_188666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188666 prefixEnd_188666 := by exact prefixLift 188666
  have htrace : WordTrace (prefixWord ++ tailWord_188666) baseStart_188666 baseEnd_188666 := by
    simpa [prefixWord, tailWord_188666, baseEnd_188666] using wordTrace_append hprefix tailTrace_188666
  have hstable : (prefixWord ++ tailWord_188666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188666).length < 2 ^ (prefixWord ++ tailWord_188666).sum := by decide
  have hdescent : baseEnd_188666 < baseStart_188666 := by decide
  rcases family_descends (prefixWord ++ tailWord_188666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188670 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_188670 : Nat := 118140960795 + 188670 * 2 ^ 59
def prefixEnd_188670 : Nat := 4983230072969 + 3 ^ 40 * 188670 * 2
def baseEnd_188670 : Nat := 86114128963450721295403

theorem tailTrace_188670 : CollatzResearch.WordTrace tailWord_188670 prefixEnd_188670 86114128963450721295403 := by
  unfold tailWord_188670
  simp only [CollatzResearch.WordTrace]
  refine ⟨860170028311035889470433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4587573484325524743842309 860170028311035889470433)
  ·
    refine ⟨645127521233276917102825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 860170028311035889470433 645127521233276917102825)
    ·
      refine ⟨483845640924957687827119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 645127521233276917102825 483845640924957687827119)
      ·
        refine ⟨725768461387436531740679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483845640924957687827119 725768461387436531740679)
        ·
          refine ⟨1088652692081154797611019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725768461387436531740679 1088652692081154797611019)
          ·
            refine ⟨1632979038121732196416529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088652692081154797611019 1632979038121732196416529)
            ·
              refine ⟨1224734278591299147312397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1632979038121732196416529 1224734278591299147312397)
              ·
                refine ⟨459275354471737180242149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1224734278591299147312397 459275354471737180242149)
                ·
                  refine ⟨86114128963450721295403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 459275354471737180242149 86114128963450721295403)
                  ·
                    rfl

theorem cell20_188670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_188670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188670 prefixEnd_188670 := by exact prefixLift 188670
  have htrace : WordTrace (prefixWord ++ tailWord_188670) baseStart_188670 baseEnd_188670 := by
    simpa [prefixWord, tailWord_188670, baseEnd_188670] using wordTrace_append hprefix tailTrace_188670
  have hstable : (prefixWord ++ tailWord_188670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188670).length < 2 ^ (prefixWord ++ tailWord_188670).sum := by decide
  have hdescent : baseEnd_188670 < baseStart_188670 := by decide
  rcases family_descends (prefixWord ++ tailWord_188670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188684 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 3]
def baseStart_188684 : Nat := 118140960795 + 188684 * 2 ^ 59
def prefixEnd_188684 : Nat := 4983230072969 + 3 ^ 40 * 188684 * 2
def baseEnd_188684 : Nat := 86120518944928894828679

theorem tailTrace_188684 : CollatzResearch.WordTrace tailWord_188684 prefixEnd_188684 86120518944928894828679 := by
  unfold tailWord_188684
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440935424218783753386553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4587913898958378337848737 3440935424218783753386553)
  ·
    refine ⟨2580701568164087815039915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3440935424218783753386553 2580701568164087815039915)
    ·
      refine ⟨3871052352246131722559873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580701568164087815039915 3871052352246131722559873)
      ·
        refine ⟨2903289264184598791919905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3871052352246131722559873 2903289264184598791919905)
        ·
          refine ⟨2177466948138449093939929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2903289264184598791919905 2177466948138449093939929)
          ·
            refine ⟨1633100211103836820454947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2177466948138449093939929 1633100211103836820454947)
            ·
              refine ⟨2449650316655755230682421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633100211103836820454947 2449650316655755230682421)
              ·
                refine ⟨229654717186477052876477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2449650316655755230682421 229654717186477052876477)
                ·
                  refine ⟨86120518944928894828679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229654717186477052876477 86120518944928894828679)
                  ·
                    rfl

theorem cell20_188684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_188684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188684 prefixEnd_188684 := by exact prefixLift 188684
  have htrace : WordTrace (prefixWord ++ tailWord_188684) baseStart_188684 baseEnd_188684 := by
    simpa [prefixWord, tailWord_188684, baseEnd_188684] using wordTrace_append hprefix tailTrace_188684
  have hstable : (prefixWord ++ tailWord_188684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188684).length < 2 ^ (prefixWord ++ tailWord_188684).sum := by decide
  have hdescent : baseEnd_188684 < baseStart_188684 := by decide
  rcases family_descends (prefixWord ++ tailWord_188684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188711 : List Nat := [1, 1, 8, 1, 1, 1, 7]
def baseStart_188711 : Nat := 118140960795 + 188711 * 2 ^ 59
def prefixEnd_188711 : Nat := 4983230072969 + 3 ^ 40 * 188711 * 2
def baseEnd_188711 : Nat := 9570315831181866769841

theorem tailTrace_188711 : CollatzResearch.WordTrace tailWord_188711 prefixEnd_188711 9570315831181866769841 := by
  unfold tailWord_188711
  simp only [CollatzResearch.WordTrace]
  refine ⟨6882855619339751118005987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4588570412893167412003991 6882855619339751118005987)
  ·
    refine ⟨10324283429009626677008981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6882855619339751118005987 10324283429009626677008981)
    ·
      refine ⟨120987696433706562621199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 10324283429009626677008981 120987696433706562621199)
      ·
        refine ⟨181481544650559843931799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120987696433706562621199 181481544650559843931799)
        ·
          refine ⟨272222316975839765897699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181481544650559843931799 272222316975839765897699)
          ·
            refine ⟨408333475463759648846549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272222316975839765897699 408333475463759648846549)
            ·
              refine ⟨9570315831181866769841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 408333475463759648846549 9570315831181866769841)
              ·
                rfl

theorem cell20_188711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 7].length) (baseStart_188711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188711 prefixEnd_188711 := by exact prefixLift 188711
  have htrace : WordTrace (prefixWord ++ tailWord_188711) baseStart_188711 baseEnd_188711 := by
    simpa [prefixWord, tailWord_188711, baseEnd_188711] using wordTrace_append hprefix tailTrace_188711
  have hstable : (prefixWord ++ tailWord_188711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188711).length < 2 ^ (prefixWord ++ tailWord_188711).sum := by decide
  have hdescent : baseEnd_188711 < baseStart_188711 := by decide
  rcases family_descends (prefixWord ++ tailWord_188711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188718 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_188718 : Nat := 118140960795 + 188718 * 2 ^ 59
def prefixEnd_188718 : Nat := 4983230072969 + 3 ^ 40 * 188718 * 2
def baseEnd_188718 : Nat := 86136037471375887695207

theorem tailTrace_188718 : CollatzResearch.WordTrace tailWord_188718 prefixEnd_188718 86136037471375887695207 := by
  unfold tailWord_188718
  simp only [CollatzResearch.WordTrace]
  refine ⟨860388866289298914188851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4588740620209594209007205 860388866289298914188851)
  ·
    refine ⟨1290583299433948371283277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 860388866289298914188851 1290583299433948371283277)
    ·
      refine ⟨483968737287730639231229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1290583299433948371283277 483968737287730639231229)
      ·
        refine ⟨181488276482898989711711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 483968737287730639231229 181488276482898989711711)
        ·
          refine ⟨272232414724348484567567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181488276482898989711711 272232414724348484567567)
          ·
            refine ⟨408348622086522726851351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272232414724348484567567 408348622086522726851351)
            ·
              refine ⟨612522933129784090277027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408348622086522726851351 612522933129784090277027)
              ·
                refine ⟨918784399694676135415541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612522933129784090277027 918784399694676135415541)
                ·
                  refine ⟨86136037471375887695207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 918784399694676135415541 86136037471375887695207)
                  ·
                    rfl

theorem cell20_188718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_188718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188718 prefixEnd_188718 := by exact prefixLift 188718
  have htrace : WordTrace (prefixWord ++ tailWord_188718) baseStart_188718 baseEnd_188718 := by
    simpa [prefixWord, tailWord_188718, baseEnd_188718] using wordTrace_append hprefix tailTrace_188718
  have hstable : (prefixWord ++ tailWord_188718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188718).length < 2 ^ (prefixWord ++ tailWord_188718).sum := by decide
  have hdescent : baseEnd_188718 < baseStart_188718 := by decide
  rcases family_descends (prefixWord ++ tailWord_188718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188753 : List Nat := [1, 2, 2, 1, 4, 2, 4, 4]
def baseStart_188753 : Nat := 118140960795 + 188753 * 2 ^ 59
def prefixEnd_188753 : Nat := 4983230072969 + 3 ^ 40 * 188753 * 2
def baseEnd_188753 : Nat := 28717337475023773842799

theorem tailTrace_188753 : CollatzResearch.WordTrace tailWord_188753 prefixEnd_188753 28717337475023773842799 := by
  unfold tailWord_188753
  simp only [CollatzResearch.WordTrace]
  refine ⟨6884387485187592291034913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4589591656791728194023275 6884387485187592291034913)
  ·
    refine ⟨5163290613890694218276185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6884387485187592291034913 5163290613890694218276185)
    ·
      refine ⟨3872467960418020663707139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5163290613890694218276185 3872467960418020663707139)
      ·
        refine ⟨5808701940627030995560709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3872467960418020663707139 5808701940627030995560709)
        ·
          refine ⟨1089131613867568311667633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5808701940627030995560709 1089131613867568311667633)
          ·
            refine ⟨816848710400676233750725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1089131613867568311667633 816848710400676233750725)
            ·
              refine ⟨153159133200126793828261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 816848710400676233750725 153159133200126793828261)
              ·
                refine ⟨28717337475023773842799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153159133200126793828261 28717337475023773842799)
                ·
                  rfl

theorem cell20_188753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 4].length) (baseStart_188753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188753 prefixEnd_188753 := by exact prefixLift 188753
  have htrace : WordTrace (prefixWord ++ tailWord_188753) baseStart_188753 baseEnd_188753 := by
    simpa [prefixWord, tailWord_188753, baseEnd_188753] using wordTrace_append hprefix tailTrace_188753
  have hstable : (prefixWord ++ tailWord_188753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188753).length < 2 ^ (prefixWord ++ tailWord_188753).sum := by decide
  have hdescent : baseEnd_188753 < baseStart_188753 := by decide
  rcases family_descends (prefixWord ++ tailWord_188753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
