import V185TrunkScan21Chunk117

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1433868 : List Nat := [2, 2, 1, 2, 2, 2, 1, 9]
def baseStart_1433868 : Nat := 118140960795 + 1433868 * 2 ^ 59
def prefixEnd_1433868 : Nat := 4983230072969 + 3 ^ 40 * 1433868 * 2
def baseEnd_1433868 : Nat := 109076070977940921267521

theorem tailTrace_1433868 : CollatzResearch.WordTrace tailWord_1433868 prefixEnd_1433868 109076070977940921267521 := by
  unfold tailWord_1433868
  simp only [CollatzResearch.WordTrace]
  refine ⟨26148731184674298001603129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34864974912899064002137505 26148731184674298001603129)
  ·
    refine ⟨19611548388505723501202347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26148731184674298001603129 19611548388505723501202347)
    ·
      refine ⟨29417322582758585251803521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19611548388505723501202347 29417322582758585251803521)
      ·
        refine ⟨22062991937068938938852641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29417322582758585251803521 22062991937068938938852641)
        ·
          refine ⟨16547243952801704204139481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22062991937068938938852641 16547243952801704204139481)
          ·
            refine ⟨12410432964601278153104611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16547243952801704204139481 12410432964601278153104611)
            ·
              refine ⟨18615649446901917229656917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12410432964601278153104611 18615649446901917229656917)
              ·
                refine ⟨109076070977940921267521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18615649446901917229656917 109076070977940921267521)
                ·
                  rfl

theorem cell21_1433868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_1433868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433868 prefixEnd_1433868 := by exact prefixLift 1433868
  have htrace : WordTrace (prefixWord ++ tailWord_1433868) baseStart_1433868 baseEnd_1433868 := by
    simpa [prefixWord, tailWord_1433868, baseEnd_1433868] using wordTrace_append hprefix tailTrace_1433868
  have hstable : (prefixWord ++ tailWord_1433868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433868).length < 2 ^ (prefixWord ++ tailWord_1433868).sum := by decide
  have hdescent : baseEnd_1433868 < baseStart_1433868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433885 : List Nat := [1, 4, 2, 3, 2, 9]
def baseStart_1433885 : Nat := 118140960795 + 1433885 * 2 ^ 59
def prefixEnd_1433885 : Nat := 4983230072969 + 3 ^ 40 * 1433885 * 2
def baseEnd_1433885 : Nat := 12119707132053130074785

theorem tailTrace_1433885 : CollatzResearch.WordTrace tailWord_1433885 prefixEnd_1433885 12119707132053130074785 := by
  unfold tailWord_1433885
  simp only [CollatzResearch.WordTrace]
  refine ⟨52298082410287007906575109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34865388273524671937716739 52298082410287007906575109)
  ·
    refine ⟨9805890451928813982482833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52298082410287007906575109 9805890451928813982482833)
    ·
      refine ⟨7354417838946610486862125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9805890451928813982482833 7354417838946610486862125)
      ·
        refine ⟨2757906689604978932573297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7354417838946610486862125 2757906689604978932573297)
        ·
          refine ⟨2068430017203734199429973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2757906689604978932573297 2068430017203734199429973)
          ·
            refine ⟨12119707132053130074785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2068430017203734199429973 12119707132053130074785)
            ·
              rfl

theorem cell21_1433885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 9].length) (baseStart_1433885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433885 prefixEnd_1433885 := by exact prefixLift 1433885
  have htrace : WordTrace (prefixWord ++ tailWord_1433885) baseStart_1433885 baseEnd_1433885 := by
    simpa [prefixWord, tailWord_1433885, baseEnd_1433885] using wordTrace_append hprefix tailTrace_1433885
  have hstable : (prefixWord ++ tailWord_1433885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433885).length < 2 ^ (prefixWord ++ tailWord_1433885).sum := by decide
  have hdescent : baseEnd_1433885 < baseStart_1433885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1433964 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 4]
def baseStart_1433964 : Nat := 118140960795 + 1433964 * 2 ^ 59
def prefixEnd_1433964 : Nat := 4983230072969 + 3 ^ 40 * 1433964 * 2
def baseEnd_1433964 : Nat := 327250121441747930202367

theorem tailTrace_1433964 : CollatzResearch.WordTrace tailWord_1433964 prefixEnd_1433964 327250121441747930202367 := by
  unfold tailWord_1433964
  simp only [CollatzResearch.WordTrace]
  refine ⟨26150481888500402199350473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34867309184667202932467297 26150481888500402199350473)
  ·
    refine ⟨19612861416375301649512855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26150481888500402199350473 19612861416375301649512855)
    ·
      refine ⟨29419292124562952474269283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19612861416375301649512855 29419292124562952474269283)
      ·
        refine ⟨44128938186844428711403925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29419292124562952474269283 44128938186844428711403925)
        ·
          refine ⟨2068543977508332595847059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44128938186844428711403925 2068543977508332595847059)
          ·
            refine ⟨3102815966262498893770589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2068543977508332595847059 3102815966262498893770589)
            ·
              refine ⟨1163555987348437085163971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3102815966262498893770589 1163555987348437085163971)
              ·
                refine ⟨1745333981022655627745957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163555987348437085163971 1745333981022655627745957)
                ·
                  refine ⟨327250121441747930202367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745333981022655627745957 327250121441747930202367)
                  ·
                    rfl

theorem cell21_1433964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_1433964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1433964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1433964 prefixEnd_1433964 := by exact prefixLift 1433964
  have htrace : WordTrace (prefixWord ++ tailWord_1433964) baseStart_1433964 baseEnd_1433964 := by
    simpa [prefixWord, tailWord_1433964, baseEnd_1433964] using wordTrace_append hprefix tailTrace_1433964
  have hstable : (prefixWord ++ tailWord_1433964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1433964).length < 2 ^ (prefixWord ++ tailWord_1433964).sum := by decide
  have hdescent : baseEnd_1433964 < baseStart_1433964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1433964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434009 : List Nat := [1, 2, 1, 2, 1, 4, 5, 2, 3]
def baseStart_1434009 : Nat := 118140960795 + 1434009 * 2 ^ 59
def prefixEnd_1434009 : Nat := 4983230072969 + 3 ^ 40 * 1434009 * 2
def baseEnd_1434009 : Nat := 327260391054837851952275

theorem tailTrace_1434009 : CollatzResearch.WordTrace tailWord_1434009 prefixEnd_1434009 327260391054837851952275 := by
  unfold tailWord_1434009
  simp only [CollatzResearch.WordTrace]
  refine ⟨52302605061837777084089081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34868403374558518056059387 52302605061837777084089081)
  ·
    refine ⟨39226953796378332813066811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52302605061837777084089081 39226953796378332813066811)
    ·
      refine ⟨58840430694567499219600217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39226953796378332813066811 58840430694567499219600217)
      ·
        refine ⟨44130323020925624414700163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58840430694567499219600217 44130323020925624414700163)
        ·
          refine ⟨66195484531388436622050245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44130323020925624414700163 66195484531388436622050245)
          ·
            refine ⟨12411653349635331866634421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66195484531388436622050245 12411653349635331866634421)
            ·
              refine ⟨1163592501528312362496977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12411653349635331866634421 1163592501528312362496977)
              ·
                refine ⟨872694376146234271872733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1163592501528312362496977 872694376146234271872733)
                ·
                  refine ⟨327260391054837851952275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 872694376146234271872733 327260391054837851952275)
                  ·
                    rfl

theorem cell21_1434009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 3].length) (baseStart_1434009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434009 prefixEnd_1434009 := by exact prefixLift 1434009
  have htrace : WordTrace (prefixWord ++ tailWord_1434009) baseStart_1434009 baseEnd_1434009 := by
    simpa [prefixWord, tailWord_1434009, baseEnd_1434009] using wordTrace_append hprefix tailTrace_1434009
  have hstable : (prefixWord ++ tailWord_1434009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434009).length < 2 ^ (prefixWord ++ tailWord_1434009).sum := by decide
  have hdescent : baseEnd_1434009 < baseStart_1434009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434020 : List Nat := [2, 3, 1, 2, 1, 1, 3, 8]
def baseStart_1434020 : Nat := 118140960795 + 1434020 * 2 ^ 59
def prefixEnd_1434020 : Nat := 4983230072969 + 3 ^ 40 * 1434020 * 2
def baseEnd_1434020 : Nat := 109087633801568092422973

theorem tailTrace_1434020 : CollatzResearch.WordTrace tailWord_1434020 prefixEnd_1434020 109087633801568092422973 := by
  unfold tailWord_1434020
  simp only [CollatzResearch.WordTrace]
  refine ⟨26151503132398962981369757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34868670843198617308493009 26151503132398962981369757)
  ·
    refine ⟨9806813674649611118013659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26151503132398962981369757 9806813674649611118013659)
    ·
      refine ⟨14710220511974416677020489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9806813674649611118013659 14710220511974416677020489)
      ·
        refine ⟨11032665383980812507765367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14710220511974416677020489 11032665383980812507765367)
        ·
          refine ⟨16548998075971218761648051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11032665383980812507765367 16548998075971218761648051)
          ·
            refine ⟨24823497113956828142472077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16548998075971218761648051 24823497113956828142472077)
            ·
              refine ⟨9308811417733810553427029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24823497113956828142472077 9308811417733810553427029)
              ·
                refine ⟨109087633801568092422973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9308811417733810553427029 109087633801568092422973)
                ·
                  rfl

theorem cell21_1434020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_1434020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434020 prefixEnd_1434020 := by exact prefixLift 1434020
  have htrace : WordTrace (prefixWord ++ tailWord_1434020) baseStart_1434020 baseEnd_1434020 := by
    simpa [prefixWord, tailWord_1434020, baseEnd_1434020] using wordTrace_append hprefix tailTrace_1434020
  have hstable : (prefixWord ++ tailWord_1434020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434020).length < 2 ^ (prefixWord ++ tailWord_1434020).sum := by decide
  have hdescent : baseEnd_1434020 < baseStart_1434020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434023 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 4]
def baseStart_1434023 : Nat := 118140960795 + 1434023 * 2 ^ 59
def prefixEnd_1434023 : Nat := 4983230072969 + 3 ^ 40 * 1434023 * 2
def baseEnd_1434023 : Nat := 327263586045576938718913

theorem tailTrace_1434023 : CollatzResearch.WordTrace tailWord_1434023 prefixEnd_1434023 327263586045576938718913 := by
  unfold tailWord_1434023
  simp only [CollatzResearch.WordTrace]
  refine ⟨52303115683787057475098723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34868743789191371650065815 52303115683787057475098723)
  ·
    refine ⟨78454673525680586212648085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52303115683787057475098723 78454673525680586212648085)
    ·
      refine ⟨3677562821516277478717879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78454673525680586212648085 3677562821516277478717879)
      ·
        refine ⟨5516344232274416218076819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3677562821516277478717879 5516344232274416218076819)
        ·
          refine ⟨8274516348411624327115229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516344232274416218076819 8274516348411624327115229)
          ·
            refine ⟨3102943630654359122668211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8274516348411624327115229 3102943630654359122668211)
            ·
              refine ⟨4654415445981538684002317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102943630654359122668211 4654415445981538684002317)
              ·
                refine ⟨1745405792243077006500869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4654415445981538684002317 1745405792243077006500869)
                ·
                  refine ⟨327263586045576938718913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745405792243077006500869 327263586045576938718913)
                  ·
                    rfl

theorem cell21_1434023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 4].length) (baseStart_1434023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434023 prefixEnd_1434023 := by exact prefixLift 1434023
  have htrace : WordTrace (prefixWord ++ tailWord_1434023) baseStart_1434023 baseEnd_1434023 := by
    simpa [prefixWord, tailWord_1434023, baseEnd_1434023] using wordTrace_append hprefix tailTrace_1434023
  have hstable : (prefixWord ++ tailWord_1434023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434023).length < 2 ^ (prefixWord ++ tailWord_1434023).sum := by decide
  have hdescent : baseEnd_1434023 < baseStart_1434023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434065 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 6]
def baseStart_1434065 : Nat := 118140960795 + 1434065 * 2 ^ 59
def prefixEnd_1434065 : Nat := 4983230072969 + 3 ^ 40 * 1434065 * 2
def baseEnd_1434065 : Nat := 327273171017794199018827

theorem tailTrace_1434065 : CollatzResearch.WordTrace tailWord_1434065 prefixEnd_1434065 327273171017794199018827 := by
  unfold tailWord_1434065
  simp only [CollatzResearch.WordTrace]
  refine ⟨52304647549634898648127649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34869765033089932432085099 52304647549634898648127649)
  ·
    refine ⟨39228485662226173986095737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52304647549634898648127649 39228485662226173986095737)
    ·
      refine ⟨29421364246669630489571803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39228485662226173986095737 29421364246669630489571803)
      ·
        refine ⟨44132046370004445734357705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29421364246669630489571803 44132046370004445734357705)
        ·
          refine ⟨33099034777503334300768279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44132046370004445734357705 33099034777503334300768279)
          ·
            refine ⟨49648552166255001451152419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33099034777503334300768279 49648552166255001451152419)
            ·
              refine ⟨74472828249382502176728629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49648552166255001451152419 74472828249382502176728629)
              ·
                refine ⟨6981827648379609579068309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74472828249382502176728629 6981827648379609579068309)
                ·
                  refine ⟨327273171017794199018827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6981827648379609579068309 327273171017794199018827)
                  ·
                    rfl

theorem cell21_1434065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_1434065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434065 prefixEnd_1434065 := by exact prefixLift 1434065
  have htrace : WordTrace (prefixWord ++ tailWord_1434065) baseStart_1434065 baseEnd_1434065 := by
    simpa [prefixWord, tailWord_1434065, baseEnd_1434065] using wordTrace_append hprefix tailTrace_1434065
  have hstable : (prefixWord ++ tailWord_1434065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434065).length < 2 ^ (prefixWord ++ tailWord_1434065).sum := by decide
  have hdescent : baseEnd_1434065 < baseStart_1434065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434116 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 4]
def baseStart_1434116 : Nat := 118140960795 + 1434116 * 2 ^ 59
def prefixEnd_1434116 : Nat := 4983230072969 + 3 ^ 40 * 1434116 * 2
def baseEnd_1434116 : Nat := 327284809912629443668723

theorem tailTrace_1434116 : CollatzResearch.WordTrace tailWord_1434116 prefixEnd_1434116 327284809912629443668723 := by
  unfold tailWord_1434116
  simp only [CollatzResearch.WordTrace]
  refine ⟨26153253836225067179117101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34871005114966756238822801 26153253836225067179117101)
  ·
    refine ⟨9807470188584400192168913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26153253836225067179117101 9807470188584400192168913)
    ·
      refine ⟨7355602641438300144126685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9807470188584400192168913 7355602641438300144126685)
      ·
        refine ⟨2758350990539362554047507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7355602641438300144126685 2758350990539362554047507)
        ·
          refine ⟨4137526485809043831071261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758350990539362554047507 4137526485809043831071261)
          ·
            refine ⟨1551572432178391436651723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4137526485809043831071261 1551572432178391436651723)
            ·
              refine ⟨2327358648267587154977585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551572432178391436651723 2327358648267587154977585)
              ·
                refine ⟨1745518986200690366233189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2327358648267587154977585 1745518986200690366233189)
                ·
                  refine ⟨327284809912629443668723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745518986200690366233189 327284809912629443668723)
                  ·
                    rfl

theorem cell21_1434116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_1434116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434116 prefixEnd_1434116 := by exact prefixLift 1434116
  have htrace : WordTrace (prefixWord ++ tailWord_1434116) baseStart_1434116 baseEnd_1434116 := by
    simpa [prefixWord, tailWord_1434116, baseEnd_1434116] using wordTrace_append hprefix tailTrace_1434116
  have hstable : (prefixWord ++ tailWord_1434116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434116).length < 2 ^ (prefixWord ++ tailWord_1434116).sum := by decide
  have hdescent : baseEnd_1434116 < baseStart_1434116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434172 : List Nat := [2, 2, 2, 2, 3, 1, 9]
def baseStart_1434172 : Nat := 118140960795 + 1434172 * 2 ^ 59
def prefixEnd_1434172 : Nat := 4983230072969 + 3 ^ 40 * 1434172 * 2
def baseEnd_1434172 : Nat := 36366398875065087859475

theorem tailTrace_1434172 : CollatzResearch.WordTrace tailWord_1434172 prefixEnd_1434172 36366398875065087859475 := by
  unfold tailWord_1434172
  simp only [CollatzResearch.WordTrace]
  refine ⟨26154275080123627961136385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34872366773498170614848513 26154275080123627961136385)
  ·
    refine ⟨19615706310092720970852289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26154275080123627961136385 19615706310092720970852289)
    ·
      refine ⟨14711779732569540728139217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19615706310092720970852289 14711779732569540728139217)
      ·
        refine ⟨11033834799427155546104413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14711779732569540728139217 11033834799427155546104413)
        ·
          refine ⟨4137688049785183329789155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11033834799427155546104413 4137688049785183329789155)
          ·
            refine ⟨6206532074677774994683733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137688049785183329789155 6206532074677774994683733)
            ·
              refine ⟨36366398875065087859475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6206532074677774994683733 36366398875065087859475)
              ·
                rfl

theorem cell21_1434172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 9].length) (baseStart_1434172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434172 prefixEnd_1434172 := by exact prefixLift 1434172
  have htrace : WordTrace (prefixWord ++ tailWord_1434172) baseStart_1434172 baseEnd_1434172 := by
    simpa [prefixWord, tailWord_1434172, baseEnd_1434172] using wordTrace_append hprefix tailTrace_1434172
  have hstable : (prefixWord ++ tailWord_1434172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434172).length < 2 ^ (prefixWord ++ tailWord_1434172).sum := by decide
  have hdescent : baseEnd_1434172 < baseStart_1434172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434189 : List Nat := [1, 6, 1, 1, 2, 1, 1, 8]
def baseStart_1434189 : Nat := 118140960795 + 1434189 * 2 ^ 59
def prefixEnd_1434189 : Nat := 4983230072969 + 3 ^ 40 * 1434189 * 2
def baseEnd_1434189 : Nat := 109100489835732512983969

theorem tailTrace_1434189 : CollatzResearch.WordTrace tailWord_1434189 prefixEnd_1434189 109100489835732512983969 := by
  unfold tailWord_1434189
  simp only [CollatzResearch.WordTrace]
  refine ⟨52309170201185667825641621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34872780134123778550427747 52309170201185667825641621)
  ·
    refine ⟨2451992353180578179326951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52309170201185667825641621 2451992353180578179326951)
    ·
      refine ⟨3677988529770867268990427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2451992353180578179326951 3677988529770867268990427)
      ·
        refine ⟨5516982794656300903485641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3677988529770867268990427 5516982794656300903485641)
        ·
          refine ⟨4137737095992225677614231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5516982794656300903485641 4137737095992225677614231)
          ·
            refine ⟨6206605643988338516421347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137737095992225677614231 6206605643988338516421347)
            ·
              refine ⟨9309908465982507774632021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6206605643988338516421347 9309908465982507774632021)
              ·
                refine ⟨109100489835732512983969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9309908465982507774632021 109100489835732512983969)
                ·
                  rfl

theorem cell21_1434189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 8].length) (baseStart_1434189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434189 prefixEnd_1434189 := by exact prefixLift 1434189
  have htrace : WordTrace (prefixWord ++ tailWord_1434189) baseStart_1434189 baseEnd_1434189 := by
    simpa [prefixWord, tailWord_1434189, baseEnd_1434189] using wordTrace_append hprefix tailTrace_1434189
  have hstable : (prefixWord ++ tailWord_1434189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434189).length < 2 ^ (prefixWord ++ tailWord_1434189).sum := by decide
  have hdescent : baseEnd_1434189 < baseStart_1434189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434237 : List Nat := [1, 4, 1, 1, 5, 1, 1, 4, 3]
def baseStart_1434237 : Nat := 118140960795 + 1434237 * 2 ^ 59
def prefixEnd_1434237 : Nat := 4983230072969 + 3 ^ 40 * 1434237 * 2
def baseEnd_1434237 : Nat := 327312423761160122151809

theorem tailTrace_1434237 : CollatzResearch.WordTrace tailWord_1434237 prefixEnd_1434237 327312423761160122151809 := by
  unfold tailWord_1434237
  simp only [CollatzResearch.WordTrace]
  refine ⟨52310920905011772023388965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34873947270007848015592643 52310920905011772023388965)
  ·
    refine ⟨9808297669689707254385431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52310920905011772023388965 9808297669689707254385431)
    ·
      refine ⟨14712446504534560881578147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9808297669689707254385431 14712446504534560881578147)
      ·
        refine ⟨22068669756801841322367221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14712446504534560881578147 22068669756801841322367221)
        ·
          refine ⟨2068937789700172623971927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22068669756801841322367221 2068937789700172623971927)
          ·
            refine ⟨3103406684550258935957891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2068937789700172623971927 3103406684550258935957891)
            ·
              refine ⟨4655110026825388403936837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103406684550258935957891 4655110026825388403936837)
              ·
                refine ⟨872833130029760325738157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4655110026825388403936837 872833130029760325738157)
                ·
                  refine ⟨327312423761160122151809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 872833130029760325738157 327312423761160122151809)
                  ·
                    rfl

theorem cell21_1434237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_1434237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434237 prefixEnd_1434237 := by exact prefixLift 1434237
  have htrace : WordTrace (prefixWord ++ tailWord_1434237) baseStart_1434237 baseEnd_1434237 := by
    simpa [prefixWord, tailWord_1434237, baseEnd_1434237] using wordTrace_append hprefix tailTrace_1434237
  have hstable : (prefixWord ++ tailWord_1434237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434237).length < 2 ^ (prefixWord ++ tailWord_1434237).sum := by decide
  have hdescent : baseEnd_1434237 < baseStart_1434237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434282 : List Nat := [3, 1, 5, 2, 1, 1, 8]
def baseStart_1434282 : Nat := 118140960795 + 1434282 * 2 ^ 59
def prefixEnd_1434282 : Nat := 4983230072969 + 3 ^ 40 * 1434282 * 2
def baseEnd_1434282 : Nat := 36369188152694449322413

theorem tailTrace_1434282 : CollatzResearch.WordTrace tailWord_1434282 prefixEnd_1434282 36369188152694449322413 := by
  unfold tailWord_1434282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13078140547462186177194275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34875041459899163139184733 13078140547462186177194275)
  ·
    refine ⟨19617210821193279265791413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13078140547462186177194275 19617210821193279265791413)
    ·
      refine ⟨1839113514486869931167945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19617210821193279265791413 1839113514486869931167945)
      ·
        refine ⟨1379335135865152448375959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1839113514486869931167945 1379335135865152448375959)
        ·
          refine ⟨2069002703797728672563939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379335135865152448375959 2069002703797728672563939)
          ·
            refine ⟨3103504055696593008845909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069002703797728672563939 3103504055696593008845909)
            ·
              refine ⟨36369188152694449322413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3103504055696593008845909 36369188152694449322413)
              ·
                rfl

theorem cell21_1434282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 8].length) (baseStart_1434282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434282 prefixEnd_1434282 := by exact prefixLift 1434282
  have htrace : WordTrace (prefixWord ++ tailWord_1434282) baseStart_1434282 baseEnd_1434282 := by
    simpa [prefixWord, tailWord_1434282, baseEnd_1434282] using wordTrace_append hprefix tailTrace_1434282
  have hstable : (prefixWord ++ tailWord_1434282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434282).length < 2 ^ (prefixWord ++ tailWord_1434282).sum := by decide
  have hdescent : baseEnd_1434282 < baseStart_1434282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434383 : List Nat := [1, 1, 2, 1, 1, 1, 5, 9]
def baseStart_1434383 : Nat := 118140960795 + 1434383 * 2 ^ 59
def prefixEnd_1434383 : Nat := 4983230072969 + 3 ^ 40 * 1434383 * 2
def baseEnd_1434383 : Nat := 109115247650098770906059

theorem tailTrace_1434383 : CollatzResearch.WordTrace tailWord_1434383 prefixEnd_1434383 109115247650098770906059 := by
  unfold tailWord_1434383
  simp only [CollatzResearch.WordTrace]
  refine ⟨52316245962482838958203803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34877497308321892638802535 52316245962482838958203803)
  ·
    refine ⟨78474368943724258437305705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52316245962482838958203803 78474368943724258437305705)
    ·
      refine ⟨58855776707793193827979279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78474368943724258437305705 58855776707793193827979279)
      ·
        refine ⟨88283665061689790741968919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58855776707793193827979279 88283665061689790741968919)
        ·
          refine ⟨132425497592534686112953379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88283665061689790741968919 132425497592534686112953379)
          ·
            refine ⟨198638246388802029169430069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132425497592534686112953379 198638246388802029169430069)
            ·
              refine ⟨18622335598950190234634069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 198638246388802029169430069 18622335598950190234634069)
              ·
                refine ⟨109115247650098770906059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18622335598950190234634069 109115247650098770906059)
                ·
                  rfl

theorem cell21_1434383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 9].length) (baseStart_1434383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434383 prefixEnd_1434383 := by exact prefixLift 1434383
  have htrace : WordTrace (prefixWord ++ tailWord_1434383) baseStart_1434383 baseEnd_1434383 := by
    simpa [prefixWord, tailWord_1434383, baseEnd_1434383] using wordTrace_append hprefix tailTrace_1434383
  have hstable : (prefixWord ++ tailWord_1434383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434383).length < 2 ^ (prefixWord ++ tailWord_1434383).sum := by decide
  have hdescent : baseEnd_1434383 < baseStart_1434383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434431 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 5]
def baseStart_1434431 : Nat := 118140960795 + 1434431 * 2 ^ 59
def prefixEnd_1434431 : Nat := 4983230072969 + 3 ^ 40 * 1434431 * 2
def baseEnd_1434431 : Nat := 327356697204258895918079

theorem tailTrace_1434431 : CollatzResearch.WordTrace tailWord_1434431 prefixEnd_1434431 327356697204258895918079 := by
  unfold tailWord_1434431
  simp only [CollatzResearch.WordTrace]
  refine ⟨52317996666308943155951147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34878664444205962103967431 52317996666308943155951147)
  ·
    refine ⟨78476994999463414733926721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52317996666308943155951147 78476994999463414733926721)
    ·
      refine ⟨58857746249597561050445041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78476994999463414733926721 58857746249597561050445041)
      ·
        refine ⟨44143309687198170787833781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58857746249597561050445041 44143309687198170787833781)
        ·
          refine ⟨4138435283174828511359417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44143309687198170787833781 4138435283174828511359417)
          ·
            refine ⟨3103826462381121383519563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4138435283174828511359417 3103826462381121383519563)
            ·
              refine ⟨4655739693571682075279345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103826462381121383519563 4655739693571682075279345)
              ·
                refine ⟨3491804770178761556459509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4655739693571682075279345 3491804770178761556459509)
                ·
                  refine ⟨327356697204258895918079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3491804770178761556459509 327356697204258895918079)
                  ·
                    rfl

theorem cell21_1434431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 5].length) (baseStart_1434431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434431 prefixEnd_1434431 := by exact prefixLift 1434431
  have htrace : WordTrace (prefixWord ++ tailWord_1434431) baseStart_1434431 baseEnd_1434431 := by
    simpa [prefixWord, tailWord_1434431, baseEnd_1434431] using wordTrace_append hprefix tailTrace_1434431
  have hstable : (prefixWord ++ tailWord_1434431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434431).length < 2 ^ (prefixWord ++ tailWord_1434431).sum := by decide
  have hdescent : baseEnd_1434431 < baseStart_1434431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434521 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 4]
def baseStart_1434521 : Nat := 118140960795 + 1434521 * 2 ^ 59
def prefixEnd_1434521 : Nat := 4983230072969 + 3 ^ 40 * 1434521 * 2
def baseEnd_1434521 : Nat := 327377236430438739417895

theorem tailTrace_1434521 : CollatzResearch.WordTrace tailWord_1434521 prefixEnd_1434521 327377236430438739417895 := by
  unfold tailWord_1434521
  simp only [CollatzResearch.WordTrace]
  refine ⟨52321279235982888526727417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34880852823988592351151611 52321279235982888526727417)
  ·
    refine ⟨39240959426987166395045563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52321279235982888526727417 39240959426987166395045563)
    ·
      refine ⟨58861439140480749592568345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39240959426987166395045563 58861439140480749592568345)
      ·
        refine ⟨44146079355360562194426259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58861439140480749592568345 44146079355360562194426259)
        ·
          refine ⟨66219119033040843291639389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44146079355360562194426259 66219119033040843291639389)
          ·
            refine ⟨24832169637390316234364771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66219119033040843291639389 24832169637390316234364771)
            ·
              refine ⟨37248254456085474351547157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24832169637390316234364771 37248254456085474351547157)
              ·
                refine ⟨1746011927629006610228773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37248254456085474351547157 1746011927629006610228773)
                ·
                  refine ⟨327377236430438739417895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1746011927629006610228773 327377236430438739417895)
                  ·
                    rfl

theorem cell21_1434521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_1434521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434521 prefixEnd_1434521 := by exact prefixLift 1434521
  have htrace : WordTrace (prefixWord ++ tailWord_1434521) baseStart_1434521 baseEnd_1434521 := by
    simpa [prefixWord, tailWord_1434521, baseEnd_1434521] using wordTrace_append hprefix tailTrace_1434521
  have hstable : (prefixWord ++ tailWord_1434521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434521).length < 2 ^ (prefixWord ++ tailWord_1434521).sum := by decide
  have hdescent : baseEnd_1434521 < baseStart_1434521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434735 : List Nat := [1, 1, 2, 1, 3, 3, 2, 5, 3]
def baseStart_1434735 : Nat := 118140960795 + 1434735 * 2 ^ 59
def prefixEnd_1434735 : Nat := 4983230072969 + 3 ^ 40 * 1434735 * 2
def baseEnd_1434735 : Nat := 327426074146021922850791

theorem tailTrace_1434735 : CollatzResearch.WordTrace tailWord_1434735 prefixEnd_1434735 327426074146021922850791 := by
  unfold tailWord_1434735
  simp only [CollatzResearch.WordTrace]
  refine ⟨52329084457207603075017659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34886056304805068716678439 52329084457207603075017659)
  ·
    refine ⟨78493626685811404612526489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52329084457207603075017659 78493626685811404612526489)
    ·
      refine ⟨58870220014358553459394867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78493626685811404612526489 58870220014358553459394867)
      ·
        refine ⟨88305330021537830189092301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58870220014358553459394867 88305330021537830189092301)
        ·
          refine ⟨33114498758076686320909613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88305330021537830189092301 33114498758076686320909613)
          ·
            refine ⟨12417937034278757370341105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33114498758076686320909613 12417937034278757370341105)
            ·
              refine ⟨9313452775709068027755829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12417937034278757370341105 9313452775709068027755829)
              ·
                refine ⟨873136197722725127602109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9313452775709068027755829 873136197722725127602109)
                ·
                  refine ⟨327426074146021922850791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873136197722725127602109 327426074146021922850791)
                  ·
                    rfl

theorem cell21_1434735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 3].length) (baseStart_1434735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434735 prefixEnd_1434735 := by exact prefixLift 1434735
  have htrace : WordTrace (prefixWord ++ tailWord_1434735) baseStart_1434735 baseEnd_1434735 := by
    simpa [prefixWord, tailWord_1434735, baseEnd_1434735] using wordTrace_append hprefix tailTrace_1434735
  have hstable : (prefixWord ++ tailWord_1434735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434735).length < 2 ^ (prefixWord ++ tailWord_1434735).sum := by decide
  have hdescent : baseEnd_1434735 < baseStart_1434735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434752 : List Nat := [2, 1, 1, 2, 1, 3, 6, 2, 3]
def baseStart_1434752 : Nat := 118140960795 + 1434752 * 2 ^ 59
def prefixEnd_1434752 : Nat := 4983230072969 + 3 ^ 40 * 1434752 * 2
def baseEnd_1434752 : Nat := 327429953777633671067423

theorem tailTrace_1434752 : CollatzResearch.WordTrace tailWord_1434752 prefixEnd_1434752 327429953777633671067423 := by
  unfold tailWord_1434752
  simp only [CollatzResearch.WordTrace]
  refine ⟨26164852249073007489193255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34886469665430676652257673 26164852249073007489193255)
  ·
    refine ⟨39247278373609511233789883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26164852249073007489193255 39247278373609511233789883)
    ·
      refine ⟨58870917560414266850684825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39247278373609511233789883 58870917560414266850684825)
      ·
        refine ⟨44153188170310700138013619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58870917560414266850684825 44153188170310700138013619)
        ·
          refine ⟨66229782255466050207020429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44153188170310700138013619 66229782255466050207020429)
          ·
            refine ⟨24836168345799768827632661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66229782255466050207020429 24836168345799768827632661)
            ·
              refine ⟨1164195391209364163795281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24836168345799768827632661 1164195391209364163795281)
              ·
                refine ⟨873146543407023122846461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1164195391209364163795281 873146543407023122846461)
                ·
                  refine ⟨327429953777633671067423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873146543407023122846461 327429953777633671067423)
                  ·
                    rfl

theorem cell21_1434752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 3].length) (baseStart_1434752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434752 prefixEnd_1434752 := by exact prefixLift 1434752
  have htrace : WordTrace (prefixWord ++ tailWord_1434752) baseStart_1434752 baseEnd_1434752 := by
    simpa [prefixWord, tailWord_1434752, baseEnd_1434752] using wordTrace_append hprefix tailTrace_1434752
  have hstable : (prefixWord ++ tailWord_1434752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434752).length < 2 ^ (prefixWord ++ tailWord_1434752).sum := by decide
  have hdescent : baseEnd_1434752 < baseStart_1434752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434766 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_1434766 : Nat := 118140960795 + 1434766 * 2 ^ 59
def prefixEnd_1434766 : Nat := 4983230072969 + 3 ^ 40 * 1434766 * 2
def baseEnd_1434766 : Nat := 327433148768372757834061

theorem tailTrace_1434766 : CollatzResearch.WordTrace tailWord_1434766 prefixEnd_1434766 327433148768372757834061 := by
  unfold tailWord_1434766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6541276890011911921174519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34886810080063530246264101 6541276890011911921174519)
  ·
    refine ⟨9811915335017867881761779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6541276890011911921174519 9811915335017867881761779)
    ·
      refine ⟨14717873002526801822642669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9811915335017867881761779 14717873002526801822642669)
      ·
        refine ⟨5519202375947550683491001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14717873002526801822642669 5519202375947550683491001)
        ·
          refine ⟨4139401781960663012618251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5519202375947550683491001 4139401781960663012618251)
          ·
            refine ⟨6209102672940994518927377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139401781960663012618251 6209102672940994518927377)
            ·
              refine ⟨4656827004705745889195533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6209102672940994518927377 4656827004705745889195533)
              ·
                refine ⟨1746310126764654708448325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4656827004705745889195533 1746310126764654708448325)
                ·
                  refine ⟨327433148768372757834061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1746310126764654708448325 327433148768372757834061)
                  ·
                    rfl

theorem cell21_1434766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_1434766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434766 prefixEnd_1434766 := by exact prefixLift 1434766
  have htrace : WordTrace (prefixWord ++ tailWord_1434766) baseStart_1434766 baseEnd_1434766 := by
    simpa [prefixWord, tailWord_1434766, baseEnd_1434766] using wordTrace_append hprefix tailTrace_1434766
  have hstable : (prefixWord ++ tailWord_1434766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434766).length < 2 ^ (prefixWord ++ tailWord_1434766).sum := by decide
  have hdescent : baseEnd_1434766 < baseStart_1434766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434876 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 4]
def baseStart_1434876 : Nat := 118140960795 + 1434876 * 2 ^ 59
def prefixEnd_1434876 : Nat := 4983230072969 + 3 ^ 40 * 1434876 * 2
def baseEnd_1434876 : Nat := 327458252267037011000503

theorem tailTrace_1434876 : CollatzResearch.WordTrace tailWord_1434876 prefixEnd_1434876 327458252267037011000503 := by
  unfold tailWord_1434876
  simp only [CollatzResearch.WordTrace]
  refine ⟨26167113574848392077950241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34889484766464522770600321 26167113574848392077950241)
  ·
    refine ⟨19625335181136294058462681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26167113574848392077950241 19625335181136294058462681)
    ·
      refine ⟨14719001385852220543847011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19625335181136294058462681 14719001385852220543847011)
      ·
        refine ⟨22078502078778330815770517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14719001385852220543847011 22078502078778330815770517)
        ·
          refine ⟨1034929784942734256989243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22078502078778330815770517 1034929784942734256989243)
          ·
            refine ⟨1552394677414101385483865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034929784942734256989243 1552394677414101385483865)
            ·
              refine ⟨1164296008060576039112899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1552394677414101385483865 1164296008060576039112899)
              ·
                refine ⟨1746444012090864058669349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164296008060576039112899 1746444012090864058669349)
                ·
                  refine ⟨327458252267037011000503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1746444012090864058669349 327458252267037011000503)
                  ·
                    rfl

theorem cell21_1434876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_1434876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434876 prefixEnd_1434876 := by exact prefixLift 1434876
  have htrace : WordTrace (prefixWord ++ tailWord_1434876) baseStart_1434876 baseEnd_1434876 := by
    simpa [prefixWord, tailWord_1434876, baseEnd_1434876] using wordTrace_append hprefix tailTrace_1434876
  have hstable : (prefixWord ++ tailWord_1434876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434876).length < 2 ^ (prefixWord ++ tailWord_1434876).sum := by decide
  have hdescent : baseEnd_1434876 < baseStart_1434876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434960 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_1434960 : Nat := 118140960795 + 1434960 * 2 ^ 59
def prefixEnd_1434960 : Nat := 4983230072969 + 3 ^ 40 * 1434960 * 2
def baseEnd_1434960 : Nat := 327477422211471531600331

theorem tailTrace_1434960 : CollatzResearch.WordTrace tailWord_1434960 prefixEnd_1434960 327477422211471531600331 := by
  unfold tailWord_1434960
  simp only [CollatzResearch.WordTrace]
  refine ⟨26168645440696233250979167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34891527254261644334638889 26168645440696233250979167)
  ·
    refine ⟨39252968161044349876468751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26168645440696233250979167 39252968161044349876468751)
    ·
      refine ⟨58879452241566524814703127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39252968161044349876468751 58879452241566524814703127)
      ·
        refine ⟨88319178362349787222054691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58879452241566524814703127 88319178362349787222054691)
        ·
          refine ⟨132478767543524680833082037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88319178362349787222054691 132478767543524680833082037)
          ·
            refine ⟨12419884457205438828101441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132478767543524680833082037 12419884457205438828101441)
            ·
              refine ⟨9314913342904079121076081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12419884457205438828101441 9314913342904079121076081)
              ·
                refine ⟨6986185007178059340807061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9314913342904079121076081 6986185007178059340807061)
                ·
                  refine ⟨327477422211471531600331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6986185007178059340807061 327477422211471531600331)
                  ·
                    rfl

theorem cell21_1434960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_1434960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434960 prefixEnd_1434960 := by exact prefixLift 1434960
  have htrace : WordTrace (prefixWord ++ tailWord_1434960) baseStart_1434960 baseEnd_1434960 := by
    simpa [prefixWord, tailWord_1434960, baseEnd_1434960] using wordTrace_append hprefix tailTrace_1434960
  have hstable : (prefixWord ++ tailWord_1434960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434960).length < 2 ^ (prefixWord ++ tailWord_1434960).sum := by decide
  have hdescent : baseEnd_1434960 < baseStart_1434960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434963 : List Nat := [1, 1, 1, 2, 1, 1, 8, 3, 3]
def baseStart_1434963 : Nat := 118140960795 + 1434963 * 2 ^ 59
def prefixEnd_1434963 : Nat := 4983230072969 + 3 ^ 40 * 1434963 * 2
def baseEnd_1434963 : Nat := 327478106852344193050325

theorem tailTrace_1434963 : CollatzResearch.WordTrace tailWord_1434963 prefixEnd_1434963 327478106852344193050325 := by
  unfold tailWord_1434963
  simp only [CollatzResearch.WordTrace]
  refine ⟨52337400300381598014317543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34891600200254398676211695 52337400300381598014317543)
  ·
    refine ⟨78506100450572397021476315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52337400300381598014317543 78506100450572397021476315)
    ·
      refine ⟨117759150675858595532214473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78506100450572397021476315 117759150675858595532214473)
      ·
        refine ⟨88319363006893946649160855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117759150675858595532214473 88319363006893946649160855)
        ·
          refine ⟨132479044510340919973741283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88319363006893946649160855 132479044510340919973741283)
          ·
            refine ⟨198718566765511379960611925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132479044510340919973741283 198718566765511379960611925)
            ·
              refine ⟨2328733204283336483913421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 198718566765511379960611925 2328733204283336483913421)
              ·
                refine ⟨873274951606251181467533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2328733204283336483913421 873274951606251181467533)
                ·
                  refine ⟨327478106852344193050325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873274951606251181467533 327478106852344193050325)
                  ·
                    rfl

theorem cell21_1434963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 3].length) (baseStart_1434963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434963 prefixEnd_1434963 := by exact prefixLift 1434963
  have htrace : WordTrace (prefixWord ++ tailWord_1434963) baseStart_1434963 baseEnd_1434963 := by
    simpa [prefixWord, tailWord_1434963, baseEnd_1434963] using wordTrace_append hprefix tailTrace_1434963
  have hstable : (prefixWord ++ tailWord_1434963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434963).length < 2 ^ (prefixWord ++ tailWord_1434963).sum := by decide
  have hdescent : baseEnd_1434963 < baseStart_1434963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1434994 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_1434994 : Nat := 118140960795 + 1434994 * 2 ^ 59
def prefixEnd_1434994 : Nat := 4983230072969 + 3 ^ 40 * 1434994 * 2
def baseEnd_1434994 : Nat := 327485181474695028033595

theorem tailTrace_1434994 : CollatzResearch.WordTrace tailWord_1434994 prefixEnd_1434994 327485181474695028033595 := by
  unfold tailWord_1434994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13084632740817322577174009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34892353975512860205797357 13084632740817322577174009)
  ·
    refine ⟨9813474555612991932880507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13084632740817322577174009 9813474555612991932880507)
    ·
      refine ⟨14720211833419487899320761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9813474555612991932880507 14720211833419487899320761)
      ·
        refine ⟨11040158875064615924490571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14720211833419487899320761 11040158875064615924490571)
        ·
          refine ⟨16560238312596923886735857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11040158875064615924490571 16560238312596923886735857)
          ·
            refine ⟨12420178734447692915051893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16560238312596923886735857 12420178734447692915051893)
            ·
              refine ⟨1164391756354471210786115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12420178734447692915051893 1164391756354471210786115)
              ·
                refine ⟨1746587634531706816179173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164391756354471210786115 1746587634531706816179173)
                ·
                  refine ⟨327485181474695028033595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1746587634531706816179173 327485181474695028033595)
                  ·
                    rfl

theorem cell21_1434994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_1434994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1434994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1434994 prefixEnd_1434994 := by exact prefixLift 1434994
  have htrace : WordTrace (prefixWord ++ tailWord_1434994) baseStart_1434994 baseEnd_1434994 := by
    simpa [prefixWord, tailWord_1434994, baseEnd_1434994] using wordTrace_append hprefix tailTrace_1434994
  have hstable : (prefixWord ++ tailWord_1434994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1434994).length < 2 ^ (prefixWord ++ tailWord_1434994).sum := by decide
  have hdescent : baseEnd_1434994 < baseStart_1434994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1434994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435039 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 5]
def baseStart_1435039 : Nat := 118140960795 + 1435039 * 2 ^ 59
def prefixEnd_1435039 : Nat := 4983230072969 + 3 ^ 40 * 1435039 * 2
def baseEnd_1435039 : Nat := 327495451087784949783503

theorem tailTrace_1435039 : CollatzResearch.WordTrace tailWord_1435039 prefixEnd_1435039 327495451087784949783503 := by
  unfold tailWord_1435039
  simp only [CollatzResearch.WordTrace]
  refine ⟨52340172248106262994084171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34893448165404175329389447 52340172248106262994084171)
  ·
    refine ⟨78510258372159394491126257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52340172248106262994084171 78510258372159394491126257)
    ·
      refine ⟨58882693779119545868344693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78510258372159394491126257 58882693779119545868344693)
      ·
        refine ⟨5520252541792457425157315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58882693779119545868344693 5520252541792457425157315)
        ·
          refine ⟨8280378812688686137735973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5520252541792457425157315 8280378812688686137735973)
          ·
            refine ⟨1552571027379128650825495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8280378812688686137735973 1552571027379128650825495)
            ·
              refine ⟨2328856541068692976238243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552571027379128650825495 2328856541068692976238243)
              ·
                refine ⟨3493284811603039464357365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328856541068692976238243 3493284811603039464357365)
                ·
                  refine ⟨327495451087784949783503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3493284811603039464357365 327495451087784949783503)
                  ·
                    rfl

theorem cell21_1435039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 5].length) (baseStart_1435039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435039 prefixEnd_1435039 := by exact prefixLift 1435039
  have htrace : WordTrace (prefixWord ++ tailWord_1435039) baseStart_1435039 baseEnd_1435039 := by
    simpa [prefixWord, tailWord_1435039, baseEnd_1435039] using wordTrace_append hprefix tailTrace_1435039
  have hstable : (prefixWord ++ tailWord_1435039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435039).length < 2 ^ (prefixWord ++ tailWord_1435039).sum := by decide
  have hdescent : baseEnd_1435039 < baseStart_1435039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435143 : List Nat := [1, 1, 4, 3, 2, 2, 8]
def baseStart_1435143 : Nat := 118140960795 + 1435143 * 2 ^ 59
def prefixEnd_1435143 : Nat := 4983230072969 + 3 ^ 40 * 1435143 * 2
def baseEnd_1435143 : Nat := 36391020589411542227773

theorem tailTrace_1435143 : CollatzResearch.WordTrace tailWord_1435143 prefixEnd_1435143 36391020589411542227773 := by
  unfold tailWord_1435143
  simp only [CollatzResearch.WordTrace]
  refine ⟨52343965439729488755870083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34895976959819659170580055 52343965439729488755870083)
  ·
    refine ⟨78515948159594233133805125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52343965439729488755870083 78515948159594233133805125)
    ·
      refine ⟨14721740279923918712588461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78515948159594233133805125 14721740279923918712588461)
      ·
        refine ⟨5520652604971469517220673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14721740279923918712588461 5520652604971469517220673)
        ·
          refine ⟨4140489453728602137915505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5520652604971469517220673 4140489453728602137915505)
          ·
            refine ⟨3105367090296451603436629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4140489453728602137915505 3105367090296451603436629)
            ·
              refine ⟨36391020589411542227773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3105367090296451603436629 36391020589411542227773)
              ·
                rfl

theorem cell21_1435143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 8].length) (baseStart_1435143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435143 prefixEnd_1435143 := by exact prefixLift 1435143
  have htrace : WordTrace (prefixWord ++ tailWord_1435143) baseStart_1435143 baseEnd_1435143 := by
    simpa [prefixWord, tailWord_1435143, baseEnd_1435143] using wordTrace_append hprefix tailTrace_1435143
  have hstable : (prefixWord ++ tailWord_1435143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435143).length < 2 ^ (prefixWord ++ tailWord_1435143).sum := by decide
  have hdescent : baseEnd_1435143 < baseStart_1435143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435146 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_1435146 : Nat := 118140960795 + 1435146 * 2 ^ 59
def prefixEnd_1435146 : Nat := 4983230072969 + 3 ^ 40 * 1435146 * 2
def baseEnd_1435146 : Nat := 327519869945576541499951

theorem tailTrace_1435146 : CollatzResearch.WordTrace tailWord_1435146 prefixEnd_1435146 327519869945576541499951 := by
  unfold tailWord_1435146
  simp only [CollatzResearch.WordTrace]
  refine ⟨13086018714679655067057323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34896049905812413512152861 13086018714679655067057323)
  ·
    refine ⟨19629028072019482600585985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13086018714679655067057323 19629028072019482600585985)
    ·
      refine ⟨14721771054014611950439489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19629028072019482600585985 14721771054014611950439489)
      ·
        refine ⟨11041328290510958962829617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14721771054014611950439489 11041328290510958962829617)
        ·
          refine ⟨8280996217883219222122213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11041328290510958962829617 8280996217883219222122213)
          ·
            refine ⟨1552686790853103604147915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8280996217883219222122213 1552686790853103604147915)
            ·
              refine ⟨2329030186279655406221873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552686790853103604147915 2329030186279655406221873)
              ·
                refine ⟨1746772639709741554666405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329030186279655406221873 1746772639709741554666405)
                ·
                  refine ⟨327519869945576541499951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1746772639709741554666405 327519869945576541499951)
                  ·
                    rfl

theorem cell21_1435146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_1435146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435146 prefixEnd_1435146 := by exact prefixLift 1435146
  have htrace : WordTrace (prefixWord ++ tailWord_1435146) baseStart_1435146 baseEnd_1435146 := by
    simpa [prefixWord, tailWord_1435146, baseEnd_1435146] using wordTrace_append hprefix tailTrace_1435146
  have hstable : (prefixWord ++ tailWord_1435146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435146).length < 2 ^ (prefixWord ++ tailWord_1435146).sum := by decide
  have hdescent : baseEnd_1435146 < baseStart_1435146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435149 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1435149 : Nat := 118140960795 + 1435149 * 2 ^ 59
def prefixEnd_1435149 : Nat := 4983230072969 + 3 ^ 40 * 1435149 * 2
def baseEnd_1435149 : Nat := 327520554586449202949945

theorem tailTrace_1435149 : CollatzResearch.WordTrace tailWord_1435149 prefixEnd_1435149 327520554586449202949945 := by
  unfold tailWord_1435149
  simp only [CollatzResearch.WordTrace]
  refine ⟨52344184277707751780588501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34896122851805167853725667 52344184277707751780588501)
  ·
    refine ⟨1226816819008775432357543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 52344184277707751780588501 1226816819008775432357543)
    ·
      refine ⟨1840225228513163148536315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226816819008775432357543 1840225228513163148536315)
      ·
        refine ⟨2760337842769744722804473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840225228513163148536315 2760337842769744722804473)
        ·
          refine ⟨2070253382077308542103355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2760337842769744722804473 2070253382077308542103355)
          ·
            refine ⟨3105380073115962813155033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070253382077308542103355 3105380073115962813155033)
            ·
              refine ⟨2329035054836972109866275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3105380073115962813155033 2329035054836972109866275)
              ·
                refine ⟨3493552582255458164799413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329035054836972109866275 3493552582255458164799413)
                ·
                  refine ⟨327520554586449202949945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3493552582255458164799413 327520554586449202949945)
                  ·
                    rfl

theorem cell21_1435149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1435149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435149 prefixEnd_1435149 := by exact prefixLift 1435149
  have htrace : WordTrace (prefixWord ++ tailWord_1435149) baseStart_1435149 baseEnd_1435149 := by
    simpa [prefixWord, tailWord_1435149, baseEnd_1435149] using wordTrace_append hprefix tailTrace_1435149
  have hstable : (prefixWord ++ tailWord_1435149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435149).length < 2 ^ (prefixWord ++ tailWord_1435149).sum := by decide
  have hdescent : baseEnd_1435149 < baseStart_1435149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435191 : List Nat := [1, 1, 3, 1, 2, 4, 3, 3, 3]
def baseStart_1435191 : Nat := 118140960795 + 1435191 * 2 ^ 59
def prefixEnd_1435191 : Nat := 4983230072969 + 3 ^ 40 * 1435191 * 2
def baseEnd_1435191 : Nat := 327530139558666463249859

theorem tailTrace_1435191 : CollatzResearch.WordTrace tailWord_1435191 prefixEnd_1435191 327530139558666463249859 := by
  unfold tailWord_1435191
  simp only [CollatzResearch.WordTrace]
  refine ⟨52345716143555592953617427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34897144095703728635744951 52345716143555592953617427)
  ·
    refine ⟨78518574215333389430426141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52345716143555592953617427 78518574215333389430426141)
    ·
      refine ⟨29444465330750021036409803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78518574215333389430426141 29444465330750021036409803)
      ·
        refine ⟨44166697996125031554614705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29444465330750021036409803 44166697996125031554614705)
        ·
          refine ⟨33125023497093773665961029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44166697996125031554614705 33125023497093773665961029)
          ·
            refine ⟨6210941905705082562367693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33125023497093773665961029 6210941905705082562367693)
            ·
              refine ⟨2329103214639405960887885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6210941905705082562367693 2329103214639405960887885)
              ·
                refine ⟨873413705489777235332957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2329103214639405960887885 873413705489777235332957)
                ·
                  refine ⟨327530139558666463249859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873413705489777235332957 327530139558666463249859)
                  ·
                    rfl

theorem cell21_1435191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 3].length) (baseStart_1435191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435191 prefixEnd_1435191 := by exact prefixLift 1435191
  have htrace : WordTrace (prefixWord ++ tailWord_1435191) baseStart_1435191 baseEnd_1435191 := by
    simpa [prefixWord, tailWord_1435191, baseEnd_1435191] using wordTrace_append hprefix tailTrace_1435191
  have hstable : (prefixWord ++ tailWord_1435191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435191).length < 2 ^ (prefixWord ++ tailWord_1435191).sum := by decide
  have hdescent : baseEnd_1435191 < baseStart_1435191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435233 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 7]
def baseStart_1435233 : Nat := 118140960795 + 1435233 * 2 ^ 59
def prefixEnd_1435233 : Nat := 4983230072969 + 3 ^ 40 * 1435233 * 2
def baseEnd_1435233 : Nat := 327539724530883723549773

theorem tailTrace_1435233 : CollatzResearch.WordTrace tailWord_1435233 prefixEnd_1435233 327539724530883723549773 := by
  unfold tailWord_1435233
  simp only [CollatzResearch.WordTrace]
  refine ⟨52347248009403434126646353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34898165339602289417764235 52347248009403434126646353)
  ·
    refine ⟨39260436007052575594984765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52347248009403434126646353 39260436007052575594984765)
    ·
      refine ⟨14722663502644715848119287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39260436007052575594984765 14722663502644715848119287)
      ·
        refine ⟨22083995253967073772178931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14722663502644715848119287 22083995253967073772178931)
        ·
          refine ⟨33125992880950610658268397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22083995253967073772178931 33125992880950610658268397)
          ·
            refine ⟨12422247330356478996850649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33125992880950610658268397 12422247330356478996850649)
            ·
              refine ⟨9316685497767359247637987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12422247330356478996850649 9316685497767359247637987)
              ·
                refine ⟨13975028246651038871456981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9316685497767359247637987 13975028246651038871456981)
                ·
                  refine ⟨327539724530883723549773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13975028246651038871456981 327539724530883723549773)
                  ·
                    rfl

theorem cell21_1435233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_1435233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435233 prefixEnd_1435233 := by exact prefixLift 1435233
  have htrace : WordTrace (prefixWord ++ tailWord_1435233) baseStart_1435233 baseEnd_1435233 := by
    simpa [prefixWord, tailWord_1435233, baseEnd_1435233] using wordTrace_append hprefix tailTrace_1435233
  have hstable : (prefixWord ++ tailWord_1435233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435233).length < 2 ^ (prefixWord ++ tailWord_1435233).sum := by decide
  have hdescent : baseEnd_1435233 < baseStart_1435233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435326 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1435326 : Nat := 118140960795 + 1435326 * 2 ^ 59
def prefixEnd_1435326 : Nat := 4983230072969 + 3 ^ 40 * 1435326 * 2
def baseEnd_1435326 : Nat := 327560948397936228499583

theorem tailTrace_1435326 : CollatzResearch.WordTrace tailWord_1435326 prefixEnd_1435326 327560948397936228499583 := by
  unfold tailWord_1435326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6543829999758313876222729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34900426665377674006521221 6543829999758313876222729)
  ·
    refine ⟨4907872499818735407167047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6543829999758313876222729 4907872499818735407167047)
    ·
      refine ⟨7361808749728103110750571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4907872499818735407167047 7361808749728103110750571)
      ·
        refine ⟨11042713124592154666125857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7361808749728103110750571 11042713124592154666125857)
        ·
          refine ⟨8282034843444115999594393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11042713124592154666125857 8282034843444115999594393)
          ·
            refine ⟨6211526132583086999695795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8282034843444115999594393 6211526132583086999695795)
            ·
              refine ⟨9317289198874630499543693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6211526132583086999695795 9317289198874630499543693)
              ·
                refine ⟨3493983449577986437328885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9317289198874630499543693 3493983449577986437328885)
                ·
                  refine ⟨327560948397936228499583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3493983449577986437328885 327560948397936228499583)
                  ·
                    rfl

theorem cell21_1435326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1435326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435326 prefixEnd_1435326 := by exact prefixLift 1435326
  have htrace : WordTrace (prefixWord ++ tailWord_1435326) baseStart_1435326 baseEnd_1435326 := by
    simpa [prefixWord, tailWord_1435326, baseEnd_1435326] using wordTrace_append hprefix tailTrace_1435326
  have hstable : (prefixWord ++ tailWord_1435326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435326).length < 2 ^ (prefixWord ++ tailWord_1435326).sum := by decide
  have hdescent : baseEnd_1435326 < baseStart_1435326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435436 : List Nat := [2, 2, 1, 1, 1, 7, 2, 2, 3]
def baseStart_1435436 : Nat := 118140960795 + 1435436 * 2 ^ 59
def prefixEnd_1435436 : Nat := 4983230072969 + 3 ^ 40 * 1435436 * 2
def baseEnd_1435436 : Nat := 327586051896600481666025

theorem tailTrace_1435436 : CollatzResearch.WordTrace tailWord_1435436 prefixEnd_1435436 327586051896600481666025 := by
  unfold tailWord_1435436
  simp only [CollatzResearch.WordTrace]
  refine ⟨26177326013833999898143081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34903101351778666530857441 26177326013833999898143081)
  ·
    refine ⟨19632994510375499923607311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26177326013833999898143081 19632994510375499923607311)
    ·
      refine ⟨29449491765563249885410967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19632994510375499923607311 29449491765563249885410967)
      ·
        refine ⟨44174237648344874828116451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29449491765563249885410967 44174237648344874828116451)
        ·
          refine ⟨66261356472517312242174677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44174237648344874828116451 66261356472517312242174677)
          ·
            refine ⟨1553000542324624505675969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 66261356472517312242174677 1553000542324624505675969)
            ·
              refine ⟨1164750406743468379256977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553000542324624505675969 1164750406743468379256977)
              ·
                refine ⟨873562805057601284442733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1164750406743468379256977 873562805057601284442733)
                ·
                  refine ⟨327586051896600481666025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873562805057601284442733 327586051896600481666025)
                  ·
                    rfl

theorem cell21_1435436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_1435436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435436 prefixEnd_1435436 := by exact prefixLift 1435436
  have htrace : WordTrace (prefixWord ++ tailWord_1435436) baseStart_1435436 baseEnd_1435436 := by
    simpa [prefixWord, tailWord_1435436, baseEnd_1435436] using wordTrace_append hprefix tailTrace_1435436
  have hstable : (prefixWord ++ tailWord_1435436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435436).length < 2 ^ (prefixWord ++ tailWord_1435436).sum := by decide
  have hdescent : baseEnd_1435436 < baseStart_1435436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435461 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 5]
def baseStart_1435461 : Nat := 118140960795 + 1435461 * 2 ^ 59
def prefixEnd_1435461 : Nat := 4983230072969 + 3 ^ 40 * 1435461 * 2
def baseEnd_1435461 : Nat := 327591757237205993749307

theorem tailTrace_1435461 : CollatzResearch.WordTrace tailWord_1435461 prefixEnd_1435461 327591757237205993749307 := by
  unfold tailWord_1435461
  simp only [CollatzResearch.WordTrace]
  refine ⟨52355563852577429065946237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34903709235051619377297491 52355563852577429065946237)
  ·
    refine ⟨19633336444716535899729839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52355563852577429065946237 19633336444716535899729839)
    ·
      refine ⟨29450004667074803849594759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19633336444716535899729839 29450004667074803849594759)
      ·
        refine ⟨44175007000612205774392139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29450004667074803849594759 44175007000612205774392139)
        ·
          refine ⟨66262510500918308661588209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44175007000612205774392139 66262510500918308661588209)
          ·
            refine ⟨49696882875688731496191157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66262510500918308661588209 49696882875688731496191157)
            ·
              refine ⟨4659082769595818577767921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49696882875688731496191157 4659082769595818577767921)
              ·
                refine ⟨3494312077196863933325941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4659082769595818577767921 3494312077196863933325941)
                ·
                  refine ⟨327591757237205993749307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3494312077196863933325941 327591757237205993749307)
                  ·
                    rfl

theorem cell21_1435461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_1435461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435461 prefixEnd_1435461 := by exact prefixLift 1435461
  have htrace : WordTrace (prefixWord ++ tailWord_1435461) baseStart_1435461 baseEnd_1435461 := by
    simpa [prefixWord, tailWord_1435461, baseEnd_1435461] using wordTrace_append hprefix tailTrace_1435461
  have hstable : (prefixWord ++ tailWord_1435461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435461).length < 2 ^ (prefixWord ++ tailWord_1435461).sum := by decide
  have hdescent : baseEnd_1435461 < baseStart_1435461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435506 : List Nat := [3, 2, 1, 2, 1, 1, 1, 10]
def baseStart_1435506 : Nat := 118140960795 + 1435506 * 2 ^ 59
def prefixEnd_1435506 : Nat := 4983230072969 + 3 ^ 40 * 1435506 * 2
def baseEnd_1435506 : Nat := 109200675616765305166405

theorem tailTrace_1435506 : CollatzResearch.WordTrace tailWord_1435506 prefixEnd_1435506 109200675616765305166405 := by
  unfold tailWord_1435506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13089301284353600437833593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34904803424942934500889581 13089301284353600437833593)
  ·
    refine ⟨9816975963265200328375195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13089301284353600437833593 9816975963265200328375195)
    ·
      refine ⟨14725463944897800492562793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9816975963265200328375195 14725463944897800492562793)
      ·
        refine ⟨11044097958673350369422095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14725463944897800492562793 11044097958673350369422095)
        ·
          refine ⟨16566146938010025554133143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11044097958673350369422095 16566146938010025554133143)
          ·
            refine ⟨24849220407015038331199715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16566146938010025554133143 24849220407015038331199715)
            ·
              refine ⟨37273830610522557496799573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24849220407015038331199715 37273830610522557496799573)
              ·
                refine ⟨109200675616765305166405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37273830610522557496799573 109200675616765305166405)
                ·
                  rfl

theorem cell21_1435506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_1435506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435506 prefixEnd_1435506 := by exact prefixLift 1435506
  have htrace : WordTrace (prefixWord ++ tailWord_1435506) baseStart_1435506 baseEnd_1435506 := by
    simpa [prefixWord, tailWord_1435506, baseEnd_1435506] using wordTrace_append hprefix tailTrace_1435506
  have hstable : (prefixWord ++ tailWord_1435506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435506).length < 2 ^ (prefixWord ++ tailWord_1435506).sum := by decide
  have hdescent : baseEnd_1435506 < baseStart_1435506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435523 : List Nat := [1, 1, 1, 3, 4, 2, 4, 5]
def baseStart_1435523 : Nat := 118140960795 + 1435523 * 2 ^ 59
def prefixEnd_1435523 : Nat := 4983230072969 + 3 ^ 40 * 1435523 * 2
def baseEnd_1435523 : Nat := 109201968827302554571949

theorem tailTrace_1435523 : CollatzResearch.WordTrace tailWord_1435523 prefixEnd_1435523 109201968827302554571949 := by
  unfold tailWord_1435523
  simp only [CollatzResearch.WordTrace]
  refine ⟨52357825178352813654703223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34905216785568542436468815 52357825178352813654703223)
  ·
    refine ⟨78536737767529220482054835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52357825178352813654703223 78536737767529220482054835)
    ·
      refine ⟨117805106651293830723082253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78536737767529220482054835 117805106651293830723082253)
      ·
        refine ⟨44176914994235186521155845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117805106651293830723082253 44176914994235186521155845)
        ·
          refine ⟨8283171561419097472716721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44176914994235186521155845 8283171561419097472716721)
          ·
            refine ⟨6212378671064323104537541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8283171561419097472716721 6212378671064323104537541)
            ·
              refine ⟨1164821000824560582100789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6212378671064323104537541 1164821000824560582100789)
              ·
                refine ⟨109201968827302554571949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1164821000824560582100789 109201968827302554571949)
                ·
                  rfl

theorem cell21_1435523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 5].length) (baseStart_1435523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435523 prefixEnd_1435523 := by exact prefixLift 1435523
  have htrace : WordTrace (prefixWord ++ tailWord_1435523) baseStart_1435523 baseEnd_1435523 := by
    simpa [prefixWord, tailWord_1435523, baseEnd_1435523] using wordTrace_append hprefix tailTrace_1435523
  have hstable : (prefixWord ++ tailWord_1435523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435523).length < 2 ^ (prefixWord ++ tailWord_1435523).sum := by decide
  have hdescent : baseEnd_1435523 < baseStart_1435523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435560 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 4]
def baseStart_1435560 : Nat := 118140960795 + 1435560 * 2 ^ 59
def prefixEnd_1435560 : Nat := 4983230072969 + 3 ^ 40 * 1435560 * 2
def baseEnd_1435560 : Nat := 327614350386003821599105

theorem tailTrace_1435560 : CollatzResearch.WordTrace tailWord_1435560 prefixEnd_1435560 327614350386003821599105 := by
  unfold tailWord_1435560
  simp only [CollatzResearch.WordTrace]
  refine ⟨26179587339609384486900067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34906116452812512649200089 26179587339609384486900067)
  ·
    refine ⟨39269381009414076730350101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26179587339609384486900067 39269381009414076730350101)
    ·
      refine ⟨1840752234816284846735161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39269381009414076730350101 1840752234816284846735161)
      ·
        refine ⟨1380564176112213635051371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1840752234816284846735161 1380564176112213635051371)
        ·
          refine ⟨2070846264168320452577057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380564176112213635051371 2070846264168320452577057)
          ·
            refine ⟨1553134698126240339432793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2070846264168320452577057 1553134698126240339432793)
            ·
              refine ⟨1164851023594680254574595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553134698126240339432793 1164851023594680254574595)
              ·
                refine ⟨1747276535392020381861893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164851023594680254574595 1747276535392020381861893)
                ·
                  refine ⟨327614350386003821599105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1747276535392020381861893 327614350386003821599105)
                  ·
                    rfl

theorem cell21_1435560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_1435560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435560 prefixEnd_1435560 := by exact prefixLift 1435560
  have htrace : WordTrace (prefixWord ++ tailWord_1435560) baseStart_1435560 baseEnd_1435560 := by
    simpa [prefixWord, tailWord_1435560, baseEnd_1435560] using wordTrace_append hprefix tailTrace_1435560
  have hstable : (prefixWord ++ tailWord_1435560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435560).length < 2 ^ (prefixWord ++ tailWord_1435560).sum := by decide
  have hdescent : baseEnd_1435560 < baseStart_1435560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435602 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_1435602 : Nat := 118140960795 + 1435602 * 2 ^ 59
def prefixEnd_1435602 : Nat := 4983230072969 + 3 ^ 40 * 1435602 * 2
def baseEnd_1435602 : Nat := 327623935358221081899019

theorem tailTrace_1435602 : CollatzResearch.WordTrace tailWord_1435602 prefixEnd_1435602 327623935358221081899019 := by
  unfold tailWord_1435602
  simp only [CollatzResearch.WordTrace]
  refine ⟨13090176636266652536707265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34907137696711073431219373 13090176636266652536707265)
  ·
    refine ⟨9817632477199989402530449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13090176636266652536707265 9817632477199989402530449)
    ·
      refine ⟨7363224357899992051897837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9817632477199989402530449 7363224357899992051897837)
      ·
        refine ⟨2761209134212497019461689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7363224357899992051897837 2761209134212497019461689)
        ·
          refine ⟨2070906850659372764596267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2761209134212497019461689 2070906850659372764596267)
          ·
            refine ⟨3106360275989059146894401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070906850659372764596267 3106360275989059146894401)
            ·
              refine ⟨2329770206991794360170801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3106360275989059146894401 2329770206991794360170801)
              ·
                refine ⟨1747327655243845770128101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329770206991794360170801 1747327655243845770128101)
                ·
                  refine ⟨327623935358221081899019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1747327655243845770128101 327623935358221081899019)
                  ·
                    rfl

theorem cell21_1435602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_1435602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435602 prefixEnd_1435602 := by exact prefixLift 1435602
  have htrace : WordTrace (prefixWord ++ tailWord_1435602) baseStart_1435602 baseEnd_1435602 := by
    simpa [prefixWord, tailWord_1435602, baseEnd_1435602] using wordTrace_append hprefix tailTrace_1435602
  have hstable : (prefixWord ++ tailWord_1435602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435602).length < 2 ^ (prefixWord ++ tailWord_1435602).sum := by decide
  have hdescent : baseEnd_1435602 < baseStart_1435602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435630 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_1435630 : Nat := 118140960795 + 1435630 * 2 ^ 59
def prefixEnd_1435630 : Nat := 4983230072969 + 3 ^ 40 * 1435630 * 2
def baseEnd_1435630 : Nat := 327630325339699255432295

theorem tailTrace_1435630 : CollatzResearch.WordTrace tailWord_1435630 prefixEnd_1435630 327630325339699255432295 := by
  unfold tailWord_1435630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6545215973620646366106043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34907818525976780619232229 6545215973620646366106043)
  ·
    refine ⟨9817823960430969549159065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6545215973620646366106043 9817823960430969549159065)
    ·
      refine ⟨7363367970323227161869299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9817823960430969549159065 7363367970323227161869299)
      ·
        refine ⟨11045051955484840742803949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7363367970323227161869299 11045051955484840742803949)
        ·
          refine ⟨4141894483306815278551481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11045051955484840742803949 4141894483306815278551481)
          ·
            refine ⟨3106420862480111458913611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4141894483306815278551481 3106420862480111458913611)
            ·
              refine ⟨4659631293720167188370417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106420862480111458913611 4659631293720167188370417)
              ·
                refine ⟨3494723470290125391277813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4659631293720167188370417 3494723470290125391277813)
                ·
                  refine ⟨327630325339699255432295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3494723470290125391277813 327630325339699255432295)
                  ·
                    rfl

theorem cell21_1435630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_1435630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435630 prefixEnd_1435630 := by exact prefixLift 1435630
  have htrace : WordTrace (prefixWord ++ tailWord_1435630) baseStart_1435630 baseEnd_1435630 := by
    simpa [prefixWord, tailWord_1435630, baseEnd_1435630] using wordTrace_append hprefix tailTrace_1435630
  have hstable : (prefixWord ++ tailWord_1435630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435630).length < 2 ^ (prefixWord ++ tailWord_1435630).sum := by decide
  have hdescent : baseEnd_1435630 < baseStart_1435630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435703 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 6]
def baseStart_1435703 : Nat := 118140960795 + 1435703 * 2 ^ 59
def prefixEnd_1435703 : Nat := 4983230072969 + 3 ^ 40 * 1435703 * 2
def baseEnd_1435703 : Nat := 327646984934267350715479

theorem tailTrace_1435703 : CollatzResearch.WordTrace tailWord_1435703 prefixEnd_1435703 327646984934267350715479 := by
  unfold tailWord_1435703
  simp only [CollatzResearch.WordTrace]
  refine ⟨52364390317700704396255763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34909593545133802930837175 52364390317700704396255763)
  ·
    refine ⟨78546585476551056594383645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52364390317700704396255763 78546585476551056594383645)
    ·
      refine ⟨29454969553706646222893867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78546585476551056594383645 29454969553706646222893867)
      ·
        refine ⟨44182454330559969334340801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29454969553706646222893867 44182454330559969334340801)
        ·
          refine ⟨33136840747919977000755601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44182454330559969334340801 33136840747919977000755601)
          ·
            refine ⟨24852630560939982750566701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33136840747919977000755601 24852630560939982750566701)
            ·
              refine ⟨9319736460352493531462513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24852630560939982750566701 9319736460352493531462513)
              ·
                refine ⟨6989802345264370148596885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9319736460352493531462513 6989802345264370148596885)
                ·
                  refine ⟨327646984934267350715479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6989802345264370148596885 327646984934267350715479)
                  ·
                    rfl

theorem cell21_1435703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_1435703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435703 prefixEnd_1435703 := by exact prefixLift 1435703
  have htrace : WordTrace (prefixWord ++ tailWord_1435703) baseStart_1435703 baseEnd_1435703 := by
    simpa [prefixWord, tailWord_1435703, baseEnd_1435703] using wordTrace_append hprefix tailTrace_1435703
  have hstable : (prefixWord ++ tailWord_1435703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435703).length < 2 ^ (prefixWord ++ tailWord_1435703).sum := by decide
  have hdescent : baseEnd_1435703 < baseStart_1435703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435861 : List Nat := [1, 3, 2, 4, 3, 1, 2, 5]
def baseStart_1435861 : Nat := 118140960795 + 1435861 * 2 ^ 59
def prefixEnd_1435861 : Nat := 4983230072969 + 3 ^ 40 * 1435861 * 2
def baseEnd_1435861 : Nat := 109227680895631395693941

theorem tailTrace_1435861 : CollatzResearch.WordTrace tailWord_1435861 prefixEnd_1435861 109227680895631395693941 := by
  unfold tailWord_1435861
  simp only [CollatzResearch.WordTrace]
  refine ⟨52370153051128297380507437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34913435367418864920338291 52370153051128297380507437)
  ·
    refine ⟨19638807394173111517690289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52370153051128297380507437 19638807394173111517690289)
    ·
      refine ⟨14729105545629833638267717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19638807394173111517690289 14729105545629833638267717)
      ·
        refine ⟨2761707289805593807175197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14729105545629833638267717 2761707289805593807175197)
        ·
          refine ⟨1035640233677097677690699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2761707289805593807175197 1035640233677097677690699)
          ·
            refine ⟨1553460350515646516536049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035640233677097677690699 1553460350515646516536049)
            ·
              refine ⟨1165095262886734887402037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553460350515646516536049 1165095262886734887402037)
              ·
                refine ⟨109227680895631395693941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1165095262886734887402037 109227680895631395693941)
                ·
                  rfl

theorem cell21_1435861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 5].length) (baseStart_1435861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435861 prefixEnd_1435861 := by exact prefixLift 1435861
  have htrace : WordTrace (prefixWord ++ tailWord_1435861) baseStart_1435861 baseEnd_1435861 := by
    simpa [prefixWord, tailWord_1435861, baseEnd_1435861] using wordTrace_append hprefix tailTrace_1435861
  have hstable : (prefixWord ++ tailWord_1435861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435861).length < 2 ^ (prefixWord ++ tailWord_1435861).sum := by decide
  have hdescent : baseEnd_1435861 < baseStart_1435861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435906 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1435906 : Nat := 118140960795 + 1435906 * 2 ^ 59
def prefixEnd_1435906 : Nat := 4983230072969 + 3 ^ 40 * 1435906 * 2
def baseEnd_1435906 : Nat := 327693312299984108831731

theorem tailTrace_1435906 : CollatzResearch.WordTrace tailWord_1435906 prefixEnd_1435906 327693312299984108831731 := by
  unfold tailWord_1435906
  simp only [CollatzResearch.WordTrace]
  refine ⟨13092948583991317516473893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34914529557310180043930381 13092948583991317516473893)
  ·
    refine ⟨2454927859498372034338855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13092948583991317516473893 2454927859498372034338855)
    ·
      refine ⟨3682391789247558051508283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2454927859498372034338855 3682391789247558051508283)
      ·
        refine ⟨5523587683871337077262425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3682391789247558051508283 5523587683871337077262425)
        ·
          refine ⟨4142690762903502807946819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5523587683871337077262425 4142690762903502807946819)
          ·
            refine ⟨6214036144355254211920229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142690762903502807946819 6214036144355254211920229)
            ·
              refine ⟨1165131777066610164735043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6214036144355254211920229 1165131777066610164735043)
              ·
                refine ⟨1747697665599915247102565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165131777066610164735043 1747697665599915247102565)
                ·
                  refine ⟨327693312299984108831731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1747697665599915247102565 327693312299984108831731)
                  ·
                    rfl

theorem cell21_1435906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1435906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435906 prefixEnd_1435906 := by exact prefixLift 1435906
  have htrace : WordTrace (prefixWord ++ tailWord_1435906) baseStart_1435906 baseEnd_1435906 := by
    simpa [prefixWord, tailWord_1435906, baseEnd_1435906] using wordTrace_append hprefix tailTrace_1435906
  have hstable : (prefixWord ++ tailWord_1435906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435906).length < 2 ^ (prefixWord ++ tailWord_1435906).sum := by decide
  have hdescent : baseEnd_1435906 < baseStart_1435906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435943 : List Nat := [1, 1, 8, 1, 2, 1, 2, 2, 3]
def baseStart_1435943 : Nat := 118140960795 + 1435943 * 2 ^ 59
def prefixEnd_1435943 : Nat := 4983230072969 + 3 ^ 40 * 1435943 * 2
def baseEnd_1435943 : Nat := 327701756204080266714989

theorem tailTrace_1435943 : CollatzResearch.WordTrace tailWord_1435943 prefixEnd_1435943 327701756204080266714989 := by
  unfold tailWord_1435943
  simp only [CollatzResearch.WordTrace]
  refine ⟨52373143836831225384992483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34915429224554150256661655 52373143836831225384992483)
  ·
    refine ⟨78559715755246838077488725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52373143836831225384992483 78559715755246838077488725)
    ·
      refine ⟨920621669006798883720571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 78559715755246838077488725 920621669006798883720571)
      ·
        refine ⟨1380932503510198325580857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920621669006798883720571 1380932503510198325580857)
        ·
          refine ⟨1035699377632648744185643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1380932503510198325580857 1035699377632648744185643)
          ·
            refine ⟨1553549066448973116278465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035699377632648744185643 1553549066448973116278465)
            ·
              refine ⟨1165161799836729837208849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553549066448973116278465 1165161799836729837208849)
              ·
                refine ⟨873871349877547377906637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165161799836729837208849 873871349877547377906637)
                ·
                  refine ⟨327701756204080266714989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873871349877547377906637 327701756204080266714989)
                  ·
                    rfl

theorem cell21_1435943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 3].length) (baseStart_1435943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435943 prefixEnd_1435943 := by exact prefixLift 1435943
  have htrace : WordTrace (prefixWord ++ tailWord_1435943) baseStart_1435943 baseEnd_1435943 := by
    simpa [prefixWord, tailWord_1435943, baseEnd_1435943] using wordTrace_append hprefix tailTrace_1435943
  have hstable : (prefixWord ++ tailWord_1435943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435943).length < 2 ^ (prefixWord ++ tailWord_1435943).sum := by decide
  have hdescent : baseEnd_1435943 < baseStart_1435943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435962 : List Nat := [3, 1, 1, 1, 4, 2, 3, 6]
def baseStart_1435962 : Nat := 118140960795 + 1435962 * 2 ^ 59
def prefixEnd_1435962 : Nat := 4983230072969 + 3 ^ 40 * 1435962 * 2
def baseEnd_1435962 : Nat := 109235364087646818632761

theorem tailTrace_1435962 : CollatzResearch.WordTrace tailWord_1435962 prefixEnd_1435962 109235364087646818632761 := by
  unfold tailWord_1435962
  simp only [CollatzResearch.WordTrace]
  refine ⟨13093459205940597907483535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34915891215841594419956093 13093459205940597907483535)
  ·
    refine ⟨19640188808910896861225303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13093459205940597907483535 19640188808910896861225303)
    ·
      refine ⟨29460283213366345291837955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19640188808910896861225303 29460283213366345291837955)
      ·
        refine ⟨44190424820049517937756933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29460283213366345291837955 44190424820049517937756933)
        ·
          refine ⟨8285704653759284613329425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44190424820049517937756933 8285704653759284613329425)
          ·
            refine ⟨6214278490319463459997069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8285704653759284613329425 6214278490319463459997069)
            ·
              refine ⟨2330354433869798797498901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6214278490319463459997069 2330354433869798797498901)
              ·
                refine ⟨109235364087646818632761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2330354433869798797498901 109235364087646818632761)
                ·
                  rfl

theorem cell21_1435962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_1435962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435962 prefixEnd_1435962 := by exact prefixLift 1435962
  have htrace : WordTrace (prefixWord ++ tailWord_1435962) baseStart_1435962 baseEnd_1435962 := by
    simpa [prefixWord, tailWord_1435962, baseEnd_1435962] using wordTrace_append hprefix tailTrace_1435962
  have hstable : (prefixWord ++ tailWord_1435962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435962).length < 2 ^ (prefixWord ++ tailWord_1435962).sum := by decide
  have hdescent : baseEnd_1435962 < baseStart_1435962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1435976 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_1435976 : Nat := 118140960795 + 1435976 * 2 ^ 59
def prefixEnd_1435976 : Nat := 4983230072969 + 3 ^ 40 * 1435976 * 2
def baseEnd_1435976 : Nat := 327709287253679542664921

theorem tailTrace_1435976 : CollatzResearch.WordTrace tailWord_1435976 prefixEnd_1435976 327709287253679542664921 := by
  unfold tailWord_1435976
  simp only [CollatzResearch.WordTrace]
  refine ⟨26187173722855836010471891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34916231630474448013962521 26187173722855836010471891)
  ·
    refine ⟨39280760584283754015707837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26187173722855836010471891 39280760584283754015707837)
    ·
      refine ⟨14730285219106407755890439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39280760584283754015707837 14730285219106407755890439)
      ·
        refine ⟨22095427828659611633835659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14730285219106407755890439 22095427828659611633835659)
        ·
          refine ⟨33143141742989417450753489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22095427828659611633835659 33143141742989417450753489)
          ·
            refine ⟨24857356307242063088065117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33143141742989417450753489 24857356307242063088065117)
            ·
              refine ⟨9321508615215773658024419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24857356307242063088065117 9321508615215773658024419)
              ·
                refine ⟨13982262922823660487036629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9321508615215773658024419 13982262922823660487036629)
                ·
                  refine ⟨327709287253679542664921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13982262922823660487036629 327709287253679542664921)
                  ·
                    rfl

theorem cell21_1435976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_1435976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1435976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1435976 prefixEnd_1435976 := by exact prefixLift 1435976
  have htrace : WordTrace (prefixWord ++ tailWord_1435976) baseStart_1435976 baseEnd_1435976 := by
    simpa [prefixWord, tailWord_1435976, baseEnd_1435976] using wordTrace_append hprefix tailTrace_1435976
  have hstable : (prefixWord ++ tailWord_1435976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1435976).length < 2 ^ (prefixWord ++ tailWord_1435976).sum := by decide
  have hdescent : baseEnd_1435976 < baseStart_1435976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1435976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436010 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_1436010 : Nat := 118140960795 + 1436010 * 2 ^ 59
def prefixEnd_1436010 : Nat := 4983230072969 + 3 ^ 40 * 1436010 * 2
def baseEnd_1436010 : Nat := 327717046516903039098185

theorem tailTrace_1436010 : CollatzResearch.WordTrace tailWord_1436010 prefixEnd_1436010 327717046516903039098185 := by
  unfold tailWord_1436010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13093896881897123956920371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34917058351725663885120989 13093896881897123956920371)
  ·
    refine ⟨19640845322845685935380557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13093896881897123956920371 19640845322845685935380557)
    ·
      refine ⟨7365316996067132225767709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19640845322845685935380557 7365316996067132225767709)
      ·
        refine ⟨2761993873525174584662891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7365316996067132225767709 2761993873525174584662891)
        ·
          refine ⟨4142990810287761876994337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2761993873525174584662891 4142990810287761876994337)
          ·
            refine ⟨3107243107715821407745753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4142990810287761876994337 3107243107715821407745753)
            ·
              refine ⟨2330432330786866055809315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3107243107715821407745753 2330432330786866055809315)
              ·
                refine ⟨3495648496180299083713973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2330432330786866055809315 3495648496180299083713973)
                ·
                  refine ⟨327717046516903039098185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3495648496180299083713973 327717046516903039098185)
                  ·
                    rfl

theorem cell21_1436010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_1436010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436010 prefixEnd_1436010 := by exact prefixLift 1436010
  have htrace : WordTrace (prefixWord ++ tailWord_1436010) baseStart_1436010 baseEnd_1436010 := by
    simpa [prefixWord, tailWord_1436010, baseEnd_1436010] using wordTrace_append hprefix tailTrace_1436010
  have hstable : (prefixWord ++ tailWord_1436010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436010).length < 2 ^ (prefixWord ++ tailWord_1436010).sum := by decide
  have hdescent : baseEnd_1436010 < baseStart_1436010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436114 : List Nat := [3, 2, 2, 4, 10]
def baseStart_1436114 : Nat := 118140960795 + 1436114 * 2 ^ 59
def prefixEnd_1436114 : Nat := 4983230072969 + 3 ^ 40 * 1436114 * 2
def baseEnd_1436114 : Nat := 4046182478195332955119

theorem tailTrace_1436114 : CollatzResearch.WordTrace tailWord_1436114 prefixEnd_1436114 4046182478195332955119 := by
  unfold tailWord_1436114
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094845179802930397366849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34919587146141147726311597 13094845179802930397366849)
  ·
    refine ⟨9821133884852197798025137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13094845179802930397366849 9821133884852197798025137)
    ·
      refine ⟨7365850413639148348518853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9821133884852197798025137 7365850413639148348518853)
      ·
        refine ⟨1381096952557340315347285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7365850413639148348518853 1381096952557340315347285)
        ·
          refine ⟨4046182478195332955119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1381096952557340315347285 4046182478195332955119)
          ·
            rfl

theorem cell21_1436114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 10].length) (baseStart_1436114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436114 prefixEnd_1436114 := by exact prefixLift 1436114
  have htrace : WordTrace (prefixWord ++ tailWord_1436114) baseStart_1436114 baseEnd_1436114 := by
    simpa [prefixWord, tailWord_1436114, baseEnd_1436114] using wordTrace_append hprefix tailTrace_1436114
  have hstable : (prefixWord ++ tailWord_1436114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436114).length < 2 ^ (prefixWord ++ tailWord_1436114).sum := by decide
  have hdescent : baseEnd_1436114 < baseStart_1436114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436128 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_1436128 : Nat := 118140960795 + 1436128 * 2 ^ 59
def prefixEnd_1436128 : Nat := 4983230072969 + 3 ^ 40 * 1436128 * 2
def baseEnd_1436128 : Nat := 327743975724561056131277

theorem tailTrace_1436128 : CollatzResearch.WordTrace tailWord_1436128 prefixEnd_1436128 327743975724561056131277 := by
  unfold tailWord_1436128
  simp only [CollatzResearch.WordTrace]
  refine ⟨26189945670580500990238519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34919927560774001320318025 26189945670580500990238519)
  ·
    refine ⟨39284918505870751485357779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26189945670580500990238519 39284918505870751485357779)
    ·
      refine ⟨58927377758806127228036669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39284918505870751485357779 58927377758806127228036669)
      ·
        refine ⟨22097766659552297710513751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58927377758806127228036669 22097766659552297710513751)
        ·
          refine ⟨33146649989328446565770627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22097766659552297710513751 33146649989328446565770627)
          ·
            refine ⟨49719974983992669848655941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33146649989328446565770627 49719974983992669848655941)
            ·
              refine ⟨9322495309498625596622989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49719974983992669848655941 9322495309498625596622989)
              ·
                refine ⟨3495935741061984598733621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9322495309498625596622989 3495935741061984598733621)
                ·
                  refine ⟨327743975724561056131277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3495935741061984598733621 327743975724561056131277)
                  ·
                    rfl

theorem cell21_1436128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_1436128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436128 prefixEnd_1436128 := by exact prefixLift 1436128
  have htrace : WordTrace (prefixWord ++ tailWord_1436128) baseStart_1436128 baseEnd_1436128 := by
    simpa [prefixWord, tailWord_1436128, baseEnd_1436128] using wordTrace_append hprefix tailTrace_1436128
  have hstable : (prefixWord ++ tailWord_1436128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436128).length < 2 ^ (prefixWord ++ tailWord_1436128).sum := by decide
  have hdescent : baseEnd_1436128 < baseStart_1436128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436131 : List Nat := [1, 1, 1, 6, 3, 2, 1, 6]
def baseStart_1436131 : Nat := 118140960795 + 1436131 * 2 ^ 59
def prefixEnd_1436131 : Nat := 4983230072969 + 3 ^ 40 * 1436131 * 2
def baseEnd_1436131 : Nat := 109248220121811239193757

theorem tailTrace_1436131 : CollatzResearch.WordTrace tailWord_1436131 prefixEnd_1436131 109248220121811239193757 := by
  unfold tailWord_1436131
  simp only [CollatzResearch.WordTrace]
  refine ⟨52380000760150133492836247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34920000506766755661890831 52380000760150133492836247)
  ·
    refine ⟨78570001140225200239254371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52380000760150133492836247 78570001140225200239254371)
    ·
      refine ⟨117855001710337800358881557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78570001140225200239254371 117855001710337800358881557)
      ·
        refine ⟨5524453205172084391822573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117855001710337800358881557 5524453205172084391822573)
        ·
          refine ⟨2071669951939531646933465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5524453205172084391822573 2071669951939531646933465)
          ·
            refine ⟨1553752463954648735200099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2071669951939531646933465 1553752463954648735200099)
            ·
              refine ⟨2330628695931973102800149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553752463954648735200099 2330628695931973102800149)
              ·
                refine ⟨109248220121811239193757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2330628695931973102800149 109248220121811239193757)
                ·
                  rfl

theorem cell21_1436131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 6].length) (baseStart_1436131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436131 prefixEnd_1436131 := by exact prefixLift 1436131
  have htrace : WordTrace (prefixWord ++ tailWord_1436131) baseStart_1436131 baseEnd_1436131 := by
    simpa [prefixWord, tailWord_1436131, baseEnd_1436131] using wordTrace_append hprefix tailTrace_1436131
  have hstable : (prefixWord ++ tailWord_1436131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436131).length < 2 ^ (prefixWord ++ tailWord_1436131).sum := by decide
  have hdescent : baseEnd_1436131 < baseStart_1436131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436311 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 4]
def baseStart_1436311 : Nat := 118140960795 + 1436311 * 2 ^ 59
def prefixEnd_1436311 : Nat := 4983230072969 + 3 ^ 40 * 1436311 * 2
def baseEnd_1436311 : Nat := 327785738817793404580903

theorem tailTrace_1436311 : CollatzResearch.WordTrace tailWord_1436311 prefixEnd_1436311 327785738817793404580903 := by
  unfold tailWord_1436311
  simp only [CollatzResearch.WordTrace]
  refine ⟨52386565899498024234388787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34924377266332016156259191 52386565899498024234388787)
  ·
    refine ⟨78579848849247036351583181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52386565899498024234388787 78579848849247036351583181)
    ·
      refine ⟨29467443318467638631843693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78579848849247036351583181 29467443318467638631843693)
      ·
        refine ⟨11050291244425364486941385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29467443318467638631843693 11050291244425364486941385)
        ·
          refine ⟨8287718433319023365206039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11050291244425364486941385 8287718433319023365206039)
          ·
            refine ⟨12431577649978535047809059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8287718433319023365206039 12431577649978535047809059)
            ·
              refine ⟨18647366474967802571713589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12431577649978535047809059 18647366474967802571713589)
              ·
                refine ⟨1748190607028231491098149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18647366474967802571713589 1748190607028231491098149)
                ·
                  refine ⟨327785738817793404580903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1748190607028231491098149 327785738817793404580903)
                  ·
                    rfl

theorem cell21_1436311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 4].length) (baseStart_1436311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436311 prefixEnd_1436311 := by exact prefixLift 1436311
  have htrace : WordTrace (prefixWord ++ tailWord_1436311) baseStart_1436311 baseEnd_1436311 := by
    simpa [prefixWord, tailWord_1436311, baseEnd_1436311] using wordTrace_append hprefix tailTrace_1436311
  have hstable : (prefixWord ++ tailWord_1436311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436311).length < 2 ^ (prefixWord ++ tailWord_1436311).sum := by decide
  have hdescent : baseEnd_1436311 < baseStart_1436311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436314 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_1436314 : Nat := 118140960795 + 1436314 * 2 ^ 59
def prefixEnd_1436314 : Nat := 4983230072969 + 3 ^ 40 * 1436314 * 2
def baseEnd_1436314 : Nat := 327786423458666066030897

theorem tailTrace_1436314 : CollatzResearch.WordTrace tailWord_1436314 prefixEnd_1436314 327786423458666066030897 := by
  unfold tailWord_1436314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13096668829621788936686999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34924450212324770497831997 13096668829621788936686999)
  ·
    refine ⟨19645003244432683405030499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13096668829621788936686999 19645003244432683405030499)
    ·
      refine ⟨29467504866649025107545749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19645003244432683405030499 29467504866649025107545749)
      ·
        refine ⟨1381289290624173051916207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29467504866649025107545749 1381289290624173051916207)
        ·
          refine ⟨2071933935936259577874311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381289290624173051916207 2071933935936259577874311)
          ·
            refine ⟨3107900903904389366811467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071933935936259577874311 3107900903904389366811467)
            ·
              refine ⟨4661851355856584050217201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107900903904389366811467 4661851355856584050217201)
              ·
                refine ⟨3496388516892438037662901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4661851355856584050217201 3496388516892438037662901)
                ·
                  refine ⟨327786423458666066030897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3496388516892438037662901 327786423458666066030897)
                  ·
                    rfl

theorem cell21_1436314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_1436314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436314 prefixEnd_1436314 := by exact prefixLift 1436314
  have htrace : WordTrace (prefixWord ++ tailWord_1436314) baseStart_1436314 baseEnd_1436314 := by
    simpa [prefixWord, tailWord_1436314, baseEnd_1436314] using wordTrace_append hprefix tailTrace_1436314
  have hstable : (prefixWord ++ tailWord_1436314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436314).length < 2 ^ (prefixWord ++ tailWord_1436314).sum := by decide
  have hdescent : baseEnd_1436314 < baseStart_1436314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436387 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 6]
def baseStart_1436387 : Nat := 118140960795 + 1436387 * 2 ^ 59
def prefixEnd_1436387 : Nat := 4983230072969 + 3 ^ 40 * 1436387 * 2
def baseEnd_1436387 : Nat := 327803083053234161314081

theorem tailTrace_1436387 : CollatzResearch.WordTrace tailWord_1436387 prefixEnd_1436387 327803083053234161314081 := by
  unfold tailWord_1436387
  simp only [CollatzResearch.WordTrace]
  refine ⟨52389337847222689214155415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34926225231481792809436943 52389337847222689214155415)
  ·
    refine ⟨78584006770834033821233123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52389337847222689214155415 78584006770834033821233123)
    ·
      refine ⟨117876010156251050731849685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78584006770834033821233123 117876010156251050731849685)
      ·
        refine ⟨2762718988037134001527727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 117876010156251050731849685 2762718988037134001527727)
        ·
          refine ⟨4144078482055701002291591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2762718988037134001527727 4144078482055701002291591)
          ·
            refine ⟨6216117723083551503437387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4144078482055701002291591 6216117723083551503437387)
            ·
              refine ⟨9324176584625327255156081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6216117723083551503437387 9324176584625327255156081)
              ·
                refine ⟨6993132438468995441367061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9324176584625327255156081 6993132438468995441367061)
                ·
                  refine ⟨327803083053234161314081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6993132438468995441367061 327803083053234161314081)
                  ·
                    rfl

theorem cell21_1436387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 6].length) (baseStart_1436387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436387 prefixEnd_1436387 := by exact prefixLift 1436387
  have htrace : WordTrace (prefixWord ++ tailWord_1436387) baseStart_1436387 baseEnd_1436387 := by
    simpa [prefixWord, tailWord_1436387, baseEnd_1436387] using wordTrace_append hprefix tailTrace_1436387
  have hstable : (prefixWord ++ tailWord_1436387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436387).length < 2 ^ (prefixWord ++ tailWord_1436387).sum := by decide
  have hdescent : baseEnd_1436387 < baseStart_1436387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436418 : List Nat := [3, 4, 1, 1, 1, 2, 1, 8]
def baseStart_1436418 : Nat := 118140960795 + 1436418 * 2 ^ 59
def prefixEnd_1436418 : Nat := 4983230072969 + 3 ^ 40 * 1436418 * 2
def baseEnd_1436418 : Nat := 109270052558528332099117

theorem tailTrace_1436418 : CollatzResearch.WordTrace tailWord_1436418 prefixEnd_1436418 109270052558528332099117 := by
  unfold tailWord_1436418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13097617127527595377133477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34926979006740254339022605 13097617127527595377133477)
  ·
    refine ⟨2455803211411424133212527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13097617127527595377133477 2455803211411424133212527)
    ·
      refine ⟨3683704817117136199818791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2455803211411424133212527 3683704817117136199818791)
      ·
        refine ⟨5525557225675704299728187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3683704817117136199818791 5525557225675704299728187)
        ·
          refine ⟨8288335838513556449592281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5525557225675704299728187 8288335838513556449592281)
          ·
            refine ⟨6216251878885167337194211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8288335838513556449592281 6216251878885167337194211)
            ·
              refine ⟨9324377818327751005791317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6216251878885167337194211 9324377818327751005791317)
              ·
                refine ⟨109270052558528332099117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9324377818327751005791317 109270052558528332099117)
                ·
                  rfl

theorem cell21_1436418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_1436418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436418 prefixEnd_1436418 := by exact prefixLift 1436418
  have htrace : WordTrace (prefixWord ++ tailWord_1436418) baseStart_1436418 baseEnd_1436418 := by
    simpa [prefixWord, tailWord_1436418, baseEnd_1436418] using wordTrace_append hprefix tailTrace_1436418
  have hstable : (prefixWord ++ tailWord_1436418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436418).length < 2 ^ (prefixWord ++ tailWord_1436418).sum := by decide
  have hdescent : baseEnd_1436418 < baseStart_1436418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436449 : List Nat := [1, 2, 3, 2, 1, 2, 2, 5, 3]
def baseStart_1436449 : Nat := 118140960795 + 1436449 * 2 ^ 59
def prefixEnd_1436449 : Nat := 4983230072969 + 3 ^ 40 * 1436449 * 2
def baseEnd_1436449 : Nat := 327817232297935831280621

theorem tailTrace_1436449 : CollatzResearch.WordTrace tailWord_1436449 prefixEnd_1436449 327817232297935831280621 := by
  unfold tailWord_1436449
  simp only [CollatzResearch.WordTrace]
  refine ⟨52391599172998073802912401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34927732781998715868608267 52391599172998073802912401)
  ·
    refine ⟨39293699379748555352184301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52391599172998073802912401 39293699379748555352184301)
    ·
      refine ⟨14735137267405708257069113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39293699379748555352184301 14735137267405708257069113)
      ·
        refine ⟨11051352950554281192801835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14735137267405708257069113 11051352950554281192801835)
        ·
          refine ⟨16577029425831421789202753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11051352950554281192801835 16577029425831421789202753)
          ·
            refine ⟨12432772069373566341902065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16577029425831421789202753 12432772069373566341902065)
            ·
              refine ⟨9324579052030174756426549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12432772069373566341902065 9324579052030174756426549)
              ·
                refine ⟨874179286127828883414989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9324579052030174756426549 874179286127828883414989)
                ·
                  refine ⟨327817232297935831280621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874179286127828883414989 327817232297935831280621)
                  ·
                    rfl

theorem cell21_1436449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 3].length) (baseStart_1436449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436449 prefixEnd_1436449 := by exact prefixLift 1436449
  have htrace : WordTrace (prefixWord ++ tailWord_1436449) baseStart_1436449 baseEnd_1436449 := by
    simpa [prefixWord, tailWord_1436449, baseEnd_1436449] using wordTrace_append hprefix tailTrace_1436449
  have hstable : (prefixWord ++ tailWord_1436449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436449).length < 2 ^ (prefixWord ++ tailWord_1436449).sum := by decide
  have hdescent : baseEnd_1436449 < baseStart_1436449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436514 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1436514 : Nat := 118140960795 + 1436514 * 2 ^ 59
def prefixEnd_1436514 : Nat := 4983230072969 + 3 ^ 40 * 1436514 * 2
def baseEnd_1436514 : Nat := 327832066183510162697155

theorem tailTrace_1436514 : CollatzResearch.WordTrace tailWord_1436514 prefixEnd_1436514 327832066183510162697155 := by
  unfold tailWord_1436514
  simp only [CollatzResearch.WordTrace]
  refine ⟨13098492479440647476007149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34929313278508393269352397 13098492479440647476007149)
  ·
    refine ⟨4911934679790242803502681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13098492479440647476007149 4911934679790242803502681)
    ·
      refine ⟨3683951009842682102627011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4911934679790242803502681 3683951009842682102627011)
      ·
        refine ⟨5525926514764023153940517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3683951009842682102627011 5525926514764023153940517)
        ·
          refine ⟨1036111221518254341363847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5525926514764023153940517 1036111221518254341363847)
          ·
            refine ⟨1554166832277381512045771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036111221518254341363847 1554166832277381512045771)
            ·
              refine ⟨2331250248416072268068657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554166832277381512045771 2331250248416072268068657)
              ·
                refine ⟨1748437686312054201051493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2331250248416072268068657 1748437686312054201051493)
                ·
                  refine ⟨327832066183510162697155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1748437686312054201051493 327832066183510162697155)
                  ·
                    rfl

theorem cell21_1436514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1436514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436514 prefixEnd_1436514 := by exact prefixLift 1436514
  have htrace : WordTrace (prefixWord ++ tailWord_1436514) baseStart_1436514 baseEnd_1436514 := by
    simpa [prefixWord, tailWord_1436514, baseEnd_1436514] using wordTrace_append hprefix tailTrace_1436514
  have hstable : (prefixWord ++ tailWord_1436514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436514).length < 2 ^ (prefixWord ++ tailWord_1436514).sum := by decide
  have hdescent : baseEnd_1436514 < baseStart_1436514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436553 : List Nat := [1, 2, 1, 1, 5, 3, 1, 7]
def baseStart_1436553 : Nat := 118140960795 + 1436553 * 2 ^ 59
def prefixEnd_1436553 : Nat := 4983230072969 + 3 ^ 40 * 1436553 * 2
def baseEnd_1436553 : Nat := 109280322171618253849025

theorem tailTrace_1436553 : CollatzResearch.WordTrace tailWord_1436553 prefixEnd_1436553 109280322171618253849025 := by
  unfold tailWord_1436553
  simp only [CollatzResearch.WordTrace]
  refine ⟨52395392364621299564698313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34930261576414199709798875 52395392364621299564698313)
  ·
    refine ⟨39296544273465974673523735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52395392364621299564698313 39296544273465974673523735)
    ·
      refine ⟨58944816410198962010285603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39296544273465974673523735 58944816410198962010285603)
      ·
        refine ⟨88417224615298443015428405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58944816410198962010285603 88417224615298443015428405)
        ·
          refine ⟨8289114807684229032696413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88417224615298443015428405 8289114807684229032696413)
          ·
            refine ⟨3108418052881585887261155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8289114807684229032696413 3108418052881585887261155)
            ·
              refine ⟨4662627079322378830891733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108418052881585887261155 4662627079322378830891733)
              ·
                refine ⟨109280322171618253849025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4662627079322378830891733 109280322171618253849025)
                ·
                  rfl

theorem cell21_1436553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 7].length) (baseStart_1436553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436553 prefixEnd_1436553 := by exact prefixLift 1436553
  have htrace : WordTrace (prefixWord ++ tailWord_1436553) baseStart_1436553 baseEnd_1436553 := by
    simpa [prefixWord, tailWord_1436553, baseEnd_1436553] using wordTrace_append hprefix tailTrace_1436553
  have hstable : (prefixWord ++ tailWord_1436553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436553).length < 2 ^ (prefixWord ++ tailWord_1436553).sum := by decide
  have hdescent : baseEnd_1436553 < baseStart_1436553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436570 : List Nat := [3, 1, 1, 4, 3, 2, 7]
def baseStart_1436570 : Nat := 118140960795 + 1436570 * 2 ^ 59
def prefixEnd_1436570 : Nat := 4983230072969 + 3 ^ 40 * 1436570 * 2
def baseEnd_1436570 : Nat := 36427205127385167751523

theorem tailTrace_1436570 : CollatzResearch.WordTrace tailWord_1436570 prefixEnd_1436570 36427205127385167751523 := by
  unfold tailWord_1436570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13099003101389927867016791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34930674937039807645378109 13099003101389927867016791)
  ·
    refine ⟨19648504652084891800525187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13099003101389927867016791 19648504652084891800525187)
    ·
      refine ⟨29472756978127337700787781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19648504652084891800525187 29472756978127337700787781)
      ·
        refine ⟨5526141933398875818897709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29472756978127337700787781 5526141933398875818897709)
        ·
          refine ⟨2072303225024578432086641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5526141933398875818897709 2072303225024578432086641)
          ·
            refine ⟨1554227418768433824064981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2072303225024578432086641 1554227418768433824064981)
            ·
              refine ⟨36427205127385167751523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1554227418768433824064981 36427205127385167751523)
              ·
                rfl

theorem cell21_1436570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 7].length) (baseStart_1436570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436570 prefixEnd_1436570 := by exact prefixLift 1436570
  have htrace : WordTrace (prefixWord ++ tailWord_1436570) baseStart_1436570 baseEnd_1436570 := by
    simpa [prefixWord, tailWord_1436570, baseEnd_1436570] using wordTrace_append hprefix tailTrace_1436570
  have hstable : (prefixWord ++ tailWord_1436570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436570).length < 2 ^ (prefixWord ++ tailWord_1436570).sum := by decide
  have hdescent : baseEnd_1436570 < baseStart_1436570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436629 : List Nat := [1, 3, 2, 3, 3, 9]
def baseStart_1436629 : Nat := 118140960795 + 1436629 * 2 ^ 59
def prefixEnd_1436629 : Nat := 4983230072969 + 3 ^ 40 * 1436629 * 2
def baseEnd_1436629 : Nat := 12142900398159093269639

theorem tailTrace_1436629 : CollatzResearch.WordTrace tailWord_1436629 prefixEnd_1436629 12142900398159093269639 := by
  unfold tailWord_1436629
  simp only [CollatzResearch.WordTrace]
  refine ⟨52398164312345964544464941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34932109541563976362976627 52398164312345964544464941)
  ·
    refine ⟨19649311617129736704174353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52398164312345964544464941 19649311617129736704174353)
    ·
      refine ⟨14736983712847302528130765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19649311617129736704174353 14736983712847302528130765)
      ·
        refine ⟨5526368892317738448049037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14736983712847302528130765 5526368892317738448049037)
        ·
          refine ⟨2072388334619151918018389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5526368892317738448049037 2072388334619151918018389)
          ·
            refine ⟨12142900398159093269639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2072388334619151918018389 12142900398159093269639)
            ·
              rfl

theorem cell21_1436629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 9].length) (baseStart_1436629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436629 prefixEnd_1436629 := by exact prefixLift 1436629
  have htrace : WordTrace (prefixWord ++ tailWord_1436629) baseStart_1436629 baseEnd_1436629 := by
    simpa [prefixWord, tailWord_1436629, baseEnd_1436629] using wordTrace_append hprefix tailTrace_1436629
  have hstable : (prefixWord ++ tailWord_1436629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436629).length < 2 ^ (prefixWord ++ tailWord_1436629).sum := by decide
  have hdescent : baseEnd_1436629 < baseStart_1436629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436677 : List Nat := [1, 3, 1, 1, 2, 3, 4, 3, 3]
def baseStart_1436677 : Nat := 118140960795 + 1436677 * 2 ^ 59
def prefixEnd_1436677 : Nat := 4983230072969 + 3 ^ 40 * 1436677 * 2
def baseEnd_1436677 : Nat := 327869265004258101480155

theorem tailTrace_1436677 : CollatzResearch.WordTrace tailWord_1436677 prefixEnd_1436677 327869265004258101480155 := by
  unfold tailWord_1436677
  simp only [CollatzResearch.WordTrace]
  refine ⟨52399915016172068742212285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34933276677448045828141523 52399915016172068742212285)
  ·
    refine ⟨19649968131064525778329607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52399915016172068742212285 19649968131064525778329607)
    ·
      refine ⟨29474952196596788667494411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19649968131064525778329607 29474952196596788667494411)
      ·
        refine ⟨44212428294895183001241617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29474952196596788667494411 44212428294895183001241617)
        ·
          refine ⟨33159321221171387250931213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44212428294895183001241617 33159321221171387250931213)
          ·
            refine ⟨12434745457939270219099205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33159321221171387250931213 12434745457939270219099205)
            ·
              refine ⟨2331514773363613166081101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12434745457939270219099205 2331514773363613166081101)
              ·
                refine ⟨874318040011354937280413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2331514773363613166081101 874318040011354937280413)
                ·
                  refine ⟨327869265004258101480155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874318040011354937280413 327869265004258101480155)
                  ·
                    rfl

theorem cell21_1436677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_1436677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436677 prefixEnd_1436677 := by exact prefixLift 1436677
  have htrace : WordTrace (prefixWord ++ tailWord_1436677) baseStart_1436677 baseEnd_1436677 := by
    simpa [prefixWord, tailWord_1436677, baseEnd_1436677] using wordTrace_append hprefix tailTrace_1436677
  have hstable : (prefixWord ++ tailWord_1436677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436677).length < 2 ^ (prefixWord ++ tailWord_1436677).sum := by decide
  have hdescent : baseEnd_1436677 < baseStart_1436677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436750 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_1436750 : Nat := 118140960795 + 1436750 * 2 ^ 59
def prefixEnd_1436750 : Nat := 4983230072969 + 3 ^ 40 * 1436750 * 2
def baseEnd_1436750 : Nat := 327885924598826196763339

theorem tailTrace_1436750 : CollatzResearch.WordTrace tailWord_1436750 prefixEnd_1436750 327885924598826196763339 := by
  unfold tailWord_1436750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550322193113450276202463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34935051696605068139746469 6550322193113450276202463)
  ·
    refine ⟨9825483289670175414303695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6550322193113450276202463 9825483289670175414303695)
    ·
      refine ⟨14738224934505263121455543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9825483289670175414303695 14738224934505263121455543)
      ·
        refine ⟨22107337401757894682183315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14738224934505263121455543 22107337401757894682183315)
        ·
          refine ⟨33161006102636842023274973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22107337401757894682183315 33161006102636842023274973)
          ·
            refine ⟨12435377288488815758728115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33161006102636842023274973 12435377288488815758728115)
            ·
              refine ⟨18653065932733223638092173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12435377288488815758728115 18653065932733223638092173)
              ·
                refine ⟨6994899724774958864284565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18653065932733223638092173 6994899724774958864284565)
                ·
                  refine ⟨327885924598826196763339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6994899724774958864284565 327885924598826196763339)
                  ·
                    rfl

theorem cell21_1436750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_1436750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436750 prefixEnd_1436750 := by exact prefixLift 1436750
  have htrace : WordTrace (prefixWord ++ tailWord_1436750) baseStart_1436750 baseEnd_1436750 := by
    simpa [prefixWord, tailWord_1436750, baseEnd_1436750] using wordTrace_append hprefix tailTrace_1436750
  have hstable : (prefixWord ++ tailWord_1436750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436750).length < 2 ^ (prefixWord ++ tailWord_1436750).sum := by decide
  have hdescent : baseEnd_1436750 < baseStart_1436750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436781 : List Nat := [1, 5, 1, 1, 2, 2, 2, 7]
def baseStart_1436781 : Nat := 118140960795 + 1436781 * 2 ^ 59
def prefixEnd_1436781 : Nat := 4983230072969 + 3 ^ 40 * 1436781 * 2
def baseEnd_1436781 : Nat := 109297666407059010582203

theorem tailTrace_1436781 : CollatzResearch.WordTrace tailWord_1436781 prefixEnd_1436781 109297666407059010582203 := by
  unfold tailWord_1436781
  simp only [CollatzResearch.WordTrace]
  refine ⟨52403708207795294503998197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34935805471863529669332131 52403708207795294503998197)
  ·
    refine ⟨4912847644480808859749831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52403708207795294503998197 4912847644480808859749831)
    ·
      refine ⟨7369271466721213289624747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4912847644480808859749831 7369271466721213289624747)
      ·
        refine ⟨11053907200081819934437121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7369271466721213289624747 11053907200081819934437121)
        ·
          refine ⟨8290430400061364950827841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11053907200081819934437121 8290430400061364950827841)
          ·
            refine ⟨6217822800046023713120881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8290430400061364950827841 6217822800046023713120881)
            ·
              refine ⟨4663367100034517784840661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6217822800046023713120881 4663367100034517784840661)
              ·
                refine ⟨109297666407059010582203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4663367100034517784840661 109297666407059010582203)
                ·
                  rfl

theorem cell21_1436781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 7].length) (baseStart_1436781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436781 prefixEnd_1436781 := by exact prefixLift 1436781
  have htrace : WordTrace (prefixWord ++ tailWord_1436781) baseStart_1436781 baseEnd_1436781 := by
    simpa [prefixWord, tailWord_1436781, baseEnd_1436781] using wordTrace_append hprefix tailTrace_1436781
  have hstable : (prefixWord ++ tailWord_1436781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436781).length < 2 ^ (prefixWord ++ tailWord_1436781).sum := by decide
  have hdescent : baseEnd_1436781 < baseStart_1436781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436860 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 4]
def baseStart_1436860 : Nat := 118140960795 + 1436860 * 2 ^ 59
def prefixEnd_1436860 : Nat := 4983230072969 + 3 ^ 40 * 1436860 * 2
def baseEnd_1436860 : Nat := 327911028097490449929781

theorem tailTrace_1436860 : CollatzResearch.WordTrace tailWord_1436860 prefixEnd_1436860 327911028097490449929781 := by
  unfold tailWord_1436860
  simp only [CollatzResearch.WordTrace]
  refine ⟨26203294787254545498062017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34937726383006060664082689 26203294787254545498062017)
  ·
    refine ⟨19652471090440909123546513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26203294787254545498062017 19652471090440909123546513)
    ·
      refine ⟨14739353317830681842659885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19652471090440909123546513 14739353317830681842659885)
      ·
        refine ⟨5527257494186505690997457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14739353317830681842659885 5527257494186505690997457)
        ·
          refine ⟨4145443120639879268248093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5527257494186505690997457 4145443120639879268248093)
          ·
            refine ⟨1554541170239954725593035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4145443120639879268248093 1554541170239954725593035)
            ·
              refine ⟨2331811755359932088389553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554541170239954725593035 2331811755359932088389553)
              ·
                refine ⟨1748858816519949066292165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2331811755359932088389553 1748858816519949066292165)
                ·
                  refine ⟨327911028097490449929781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1748858816519949066292165 327911028097490449929781)
                  ·
                    rfl

theorem cell21_1436860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_1436860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436860 prefixEnd_1436860 := by exact prefixLift 1436860
  have htrace : WordTrace (prefixWord ++ tailWord_1436860) baseStart_1436860 baseEnd_1436860 := by
    simpa [prefixWord, tailWord_1436860, baseEnd_1436860] using wordTrace_append hprefix tailTrace_1436860
  have hstable : (prefixWord ++ tailWord_1436860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436860).length < 2 ^ (prefixWord ++ tailWord_1436860).sum := by decide
  have hdescent : baseEnd_1436860 < baseStart_1436860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1436981 : List Nat := [1, 3, 3, 1, 2, 3, 1, 4, 3]
def baseStart_1436981 : Nat := 118140960795 + 1436981 * 2 ^ 59
def prefixEnd_1436981 : Nat := 4983230072969 + 3 ^ 40 * 1436981 * 2
def baseEnd_1436981 : Nat := 327938641946021128412867

theorem tailTrace_1436981 : CollatzResearch.WordTrace tailWord_1436981 prefixEnd_1436981 327938641946021128412867 := by
  unfold tailWord_1436981
  simp only [CollatzResearch.WordTrace]
  refine ⟨52411002807070728661278797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34940668538047152440852531 52411002807070728661278797)
  ·
    refine ⟨19654126052651523247979549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52411002807070728661278797 19654126052651523247979549)
    ·
      refine ⟨7370297269744321217992331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19654126052651523247979549 7370297269744321217992331)
      ·
        refine ⟨11055445904616481826988497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7370297269744321217992331 11055445904616481826988497)
        ·
          refine ⟨8291584428462361370241373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11055445904616481826988497 8291584428462361370241373)
          ·
            refine ⟨3109344160673385513840515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8291584428462361370241373 3109344160673385513840515)
            ·
              refine ⟨4664016241010078270760773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3109344160673385513840515 4664016241010078270760773)
              ·
                refine ⟨874503045189389675767645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4664016241010078270760773 874503045189389675767645)
                ·
                  refine ⟨327938641946021128412867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874503045189389675767645 327938641946021128412867)
                  ·
                    rfl

theorem cell21_1436981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_1436981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1436981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1436981 prefixEnd_1436981 := by exact prefixLift 1436981
  have htrace : WordTrace (prefixWord ++ tailWord_1436981) baseStart_1436981 baseEnd_1436981 := by
    simpa [prefixWord, tailWord_1436981, baseEnd_1436981] using wordTrace_append hprefix tailTrace_1436981
  have hstable : (prefixWord ++ tailWord_1436981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1436981).length < 2 ^ (prefixWord ++ tailWord_1436981).sum := by decide
  have hdescent : baseEnd_1436981 < baseStart_1436981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1436981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437009 : List Nat := [1, 2, 2, 1, 4, 1, 5, 5]
def baseStart_1437009 : Nat := 118140960795 + 1437009 * 2 ^ 59
def prefixEnd_1437009 : Nat := 4983230072969 + 3 ^ 40 * 1437009 * 2
def baseEnd_1437009 : Nat := 109315010642499767315381

theorem tailTrace_1437009 : CollatzResearch.WordTrace tailWord_1437009 prefixEnd_1437009 109315010642499767315381 := by
  unfold tailWord_1437009
  simp only [CollatzResearch.WordTrace]
  refine ⟨52412024050969289443298081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34941349367312859628865387 52412024050969289443298081)
  ·
    refine ⟨39309018038226967082473561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52412024050969289443298081 39309018038226967082473561)
    ·
      refine ⟨29481763528670225311855171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39309018038226967082473561 29481763528670225311855171)
      ·
        refine ⟨44222645293005337967782757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29481763528670225311855171 44222645293005337967782757)
        ·
          refine ⟨8291745992438500868959267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44222645293005337967782757 8291745992438500868959267)
          ·
            refine ⟨12437618988657751303438901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8291745992438500868959267 12437618988657751303438901)
            ·
              refine ⟨1166026780186664184697397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12437618988657751303438901 1166026780186664184697397)
              ·
                refine ⟨109315010642499767315381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1166026780186664184697397 109315010642499767315381)
                ·
                  rfl

theorem cell21_1437009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 5].length) (baseStart_1437009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437009 prefixEnd_1437009 := by exact prefixLift 1437009
  have htrace : WordTrace (prefixWord ++ tailWord_1437009) baseStart_1437009 baseEnd_1437009 := by
    simpa [prefixWord, tailWord_1437009, baseEnd_1437009] using wordTrace_append hprefix tailTrace_1437009
  have hstable : (prefixWord ++ tailWord_1437009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437009).length < 2 ^ (prefixWord ++ tailWord_1437009).sum := by decide
  have hdescent : baseEnd_1437009 < baseStart_1437009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437040 : List Nat := [2, 1, 1, 1, 4, 2, 1, 6, 3]
def baseStart_1437040 : Nat := 118140960795 + 1437040 * 2 ^ 59
def prefixEnd_1437040 : Nat := 4983230072969 + 3 ^ 40 * 1437040 * 2
def baseEnd_1437040 : Nat := 327952106549850136929413

theorem tailTrace_1437040 : CollatzResearch.WordTrace tailWord_1437040 prefixEnd_1437040 327952106549850136929413 := by
  unfold tailWord_1437040
  simp only [CollatzResearch.WordTrace]
  refine ⟨26206577356928490868838287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34942103142571321158451049 26206577356928490868838287)
  ·
    refine ⟨39309866035392736303257431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26206577356928490868838287 39309866035392736303257431)
    ·
      refine ⟨58964799053089104454886147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39309866035392736303257431 58964799053089104454886147)
      ·
        refine ⟨88447198579633656682329221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58964799053089104454886147 88447198579633656682329221)
        ·
          refine ⟨16583849733681310627936729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88447198579633656682329221 16583849733681310627936729)
          ·
            refine ⟨12437887300260982970952547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16583849733681310627936729 12437887300260982970952547)
            ·
              refine ⟨18656830950391474456428821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12437887300260982970952547 18656830950391474456428821)
              ·
                refine ⟨874538950799600365145101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18656830950391474456428821 874538950799600365145101)
                ·
                  refine ⟨327952106549850136929413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874538950799600365145101 327952106549850136929413)
                  ·
                    rfl

theorem cell21_1437040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 3].length) (baseStart_1437040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437040 prefixEnd_1437040 := by exact prefixLift 1437040
  have htrace : WordTrace (prefixWord ++ tailWord_1437040) baseStart_1437040 baseEnd_1437040 := by
    simpa [prefixWord, tailWord_1437040, baseEnd_1437040] using wordTrace_append hprefix tailTrace_1437040
  have hstable : (prefixWord ++ tailWord_1437040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437040).length < 2 ^ (prefixWord ++ tailWord_1437040).sum := by decide
  have hdescent : baseEnd_1437040 < baseStart_1437040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437068 : List Nat := [2, 2, 1, 2, 1, 3, 3, 7]
def baseStart_1437068 : Nat := 118140960795 + 1437068 * 2 ^ 59
def prefixEnd_1437068 : Nat := 4983230072969 + 3 ^ 40 * 1437068 * 2
def baseEnd_1437068 : Nat := 109319498843776103487563

theorem tailTrace_1437068 : CollatzResearch.WordTrace tailWord_1437068 prefixEnd_1437068 109319498843776103487563 := by
  unfold tailWord_1437068
  simp only [CollatzResearch.WordTrace]
  refine ⟨26207087978877771259847929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34942783971837028346463905 26207087978877771259847929)
  ·
    refine ⟨19655315984158328444885947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26207087978877771259847929 19655315984158328444885947)
    ·
      refine ⟨29482973976237492667328921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19655315984158328444885947 29482973976237492667328921)
      ·
        refine ⟨22112230482178119500496691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29482973976237492667328921 22112230482178119500496691)
        ·
          refine ⟨33168345723267179250745037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22112230482178119500496691 33168345723267179250745037)
          ·
            refine ⟨12438129646225192219029389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33168345723267179250745037 12438129646225192219029389)
            ·
              refine ⟨4664298617334447082136021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12438129646225192219029389 4664298617334447082136021)
              ·
                refine ⟨109319498843776103487563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4664298617334447082136021 109319498843776103487563)
                ·
                  rfl

theorem cell21_1437068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_1437068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437068 prefixEnd_1437068 := by exact prefixLift 1437068
  have htrace : WordTrace (prefixWord ++ tailWord_1437068) baseStart_1437068 baseEnd_1437068 := by
    simpa [prefixWord, tailWord_1437068, baseEnd_1437068] using wordTrace_append hprefix tailTrace_1437068
  have hstable : (prefixWord ++ tailWord_1437068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437068).length < 2 ^ (prefixWord ++ tailWord_1437068).sum := by decide
  have hdescent : baseEnd_1437068 < baseStart_1437068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437085 : List Nat := [1, 4, 2, 1, 3, 3, 7]
def baseStart_1437085 : Nat := 118140960795 + 1437085 * 2 ^ 59
def prefixEnd_1437085 : Nat := 4983230072969 + 3 ^ 40 * 1437085 * 2
def baseEnd_1437085 : Nat := 36440264018104450964369

theorem tailTrace_1437085 : CollatzResearch.WordTrace tailWord_1437085 prefixEnd_1437085 36440264018104450964369 := by
  unfold tailWord_1437085
  simp only [CollatzResearch.WordTrace]
  refine ⟨52414795998693954423064709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34943197332462636282043139 52414795998693954423064709)
  ·
    refine ⟨9827774249755116454324633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52414795998693954423064709 9827774249755116454324633)
    ·
      refine ⟨7370830687316337340743475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9827774249755116454324633 7370830687316337340743475)
      ·
        refine ⟨11056246030974506011115213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7370830687316337340743475 11056246030974506011115213)
        ·
          refine ⟨4146092261615439754168205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11056246030974506011115213 4146092261615439754168205)
          ·
            refine ⟨1554784598105789907813077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4146092261615439754168205 1554784598105789907813077)
            ·
              refine ⟨36440264018104450964369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1554784598105789907813077 36440264018104450964369)
              ·
                rfl

theorem cell21_1437085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 7].length) (baseStart_1437085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437085 prefixEnd_1437085 := by exact prefixLift 1437085
  have htrace : WordTrace (prefixWord ++ tailWord_1437085) baseStart_1437085 baseEnd_1437085 := by
    simpa [prefixWord, tailWord_1437085, baseEnd_1437085] using wordTrace_append hprefix tailTrace_1437085
  have hstable : (prefixWord ++ tailWord_1437085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437085).length < 2 ^ (prefixWord ++ tailWord_1437085).sum := by decide
  have hdescent : baseEnd_1437085 < baseStart_1437085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437189 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 6]
def baseStart_1437189 : Nat := 118140960795 + 1437189 * 2 ^ 59
def prefixEnd_1437189 : Nat := 4983230072969 + 3 ^ 40 * 1437189 * 2
def baseEnd_1437189 : Nat := 327986110379858988945775

theorem tailTrace_1437189 : CollatzResearch.WordTrace tailWord_1437189 prefixEnd_1437189 327986110379858988945775 := by
  unfold tailWord_1437189
  simp only [CollatzResearch.WordTrace]
  refine ⟨52418589190317180184850621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34945726126878120123233747 52418589190317180184850621)
  ·
    refine ⟨19656970946368942569318983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52418589190317180184850621 19656970946368942569318983)
    ·
      refine ⟨29485456419553413853978475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19656970946368942569318983 29485456419553413853978475)
      ·
        refine ⟨44228184629330120780967713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29485456419553413853978475 44228184629330120780967713)
        ·
          refine ⟨33171138471997590585725785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44228184629330120780967713 33171138471997590585725785)
          ·
            refine ⟨24878353853998192939294339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33171138471997590585725785 24878353853998192939294339)
            ·
              refine ⟨37317530780997289408941509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24878353853998192939294339 37317530780997289408941509)
              ·
                refine ⟨6997037021436991764176533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37317530780997289408941509 6997037021436991764176533)
                ·
                  refine ⟨327986110379858988945775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6997037021436991764176533 327986110379858988945775)
                  ·
                    rfl

theorem cell21_1437189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_1437189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437189 prefixEnd_1437189 := by exact prefixLift 1437189
  have htrace : WordTrace (prefixWord ++ tailWord_1437189) baseStart_1437189 baseEnd_1437189 := by
    simpa [prefixWord, tailWord_1437189, baseEnd_1437189] using wordTrace_append hprefix tailTrace_1437189
  have hstable : (prefixWord ++ tailWord_1437189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437189).length < 2 ^ (prefixWord ++ tailWord_1437189).sum := by decide
  have hdescent : baseEnd_1437189 < baseStart_1437189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437192 : List Nat := [2, 1, 3, 2, 1, 1, 3, 5, 3]
def baseStart_1437192 : Nat := 118140960795 + 1437192 * 2 ^ 59
def prefixEnd_1437192 : Nat := 4983230072969 + 3 ^ 40 * 1437192 * 2
def baseEnd_1437192 : Nat := 327986795020731650395769

theorem tailTrace_1437192 : CollatzResearch.WordTrace tailWord_1437192 prefixEnd_1437192 327986795020731650395769 := by
  unfold tailWord_1437192
  simp only [CollatzResearch.WordTrace]
  refine ⟨26209349304653155848604915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34945799072870874464806553 26209349304653155848604915)
  ·
    refine ⟨39314023956979733772907373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26209349304653155848604915 39314023956979733772907373)
    ·
      refine ⟨14742758983867400164840265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39314023956979733772907373 14742758983867400164840265)
      ·
        refine ⟨11057069237900550123630199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14742758983867400164840265 11057069237900550123630199)
        ·
          refine ⟨16585603856850825185445299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11057069237900550123630199 16585603856850825185445299)
          ·
            refine ⟨24878405785276237778167949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16585603856850825185445299 24878405785276237778167949)
            ·
              refine ⟨9329402169478589166812981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24878405785276237778167949 9329402169478589166812981)
              ·
                refine ⟨874631453388617734388717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9329402169478589166812981 874631453388617734388717)
                ·
                  refine ⟨327986795020731650395769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874631453388617734388717 327986795020731650395769)
                  ·
                    rfl

theorem cell21_1437192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 3].length) (baseStart_1437192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437192 prefixEnd_1437192 := by exact prefixLift 1437192
  have htrace : WordTrace (prefixWord ++ tailWord_1437192) baseStart_1437192 baseEnd_1437192 := by
    simpa [prefixWord, tailWord_1437192, baseEnd_1437192] using wordTrace_append hprefix tailTrace_1437192
  have hstable : (prefixWord ++ tailWord_1437192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437192).length < 2 ^ (prefixWord ++ tailWord_1437192).sum := by decide
  have hdescent : baseEnd_1437192 < baseStart_1437192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437237 : List Nat := [1, 3, 3, 1, 1, 3, 4, 5]
def baseStart_1437237 : Nat := 118140960795 + 1437237 * 2 ^ 59
def prefixEnd_1437237 : Nat := 4983230072969 + 3 ^ 40 * 1437237 * 2
def baseEnd_1437237 : Nat := 109332354877940524048559

theorem tailTrace_1437237 : CollatzResearch.WordTrace tailWord_1437237 prefixEnd_1437237 109332354877940524048559 := by
  unfold tailWord_1437237
  simp only [CollatzResearch.WordTrace]
  refine ⟨52420339894143284382597965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34946893262762189588398643 52420339894143284382597965)
  ·
    refine ⟨19657627460303731643474237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52420339894143284382597965 19657627460303731643474237)
    ·
      refine ⟨7371610297613899366302839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19657627460303731643474237 7371610297613899366302839)
      ·
        refine ⟨11057415446420849049454259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7371610297613899366302839 11057415446420849049454259)
        ·
          refine ⟨16586123169631273574181389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11057415446420849049454259 16586123169631273574181389)
          ·
            refine ⟨6219796188611727590318021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16586123169631273574181389 6219796188611727590318021)
            ·
              refine ⟨1166211785364698923184629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6219796188611727590318021 1166211785364698923184629)
              ·
                refine ⟨109332354877940524048559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1166211785364698923184629 109332354877940524048559)
                ·
                  rfl

theorem cell21_1437237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 5].length) (baseStart_1437237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437237 prefixEnd_1437237 := by exact prefixLift 1437237
  have htrace : WordTrace (prefixWord ++ tailWord_1437237) baseStart_1437237 baseEnd_1437237 := by
    simpa [prefixWord, tailWord_1437237, baseEnd_1437237] using wordTrace_append hprefix tailTrace_1437237
  have hstable : (prefixWord ++ tailWord_1437237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437237).length < 2 ^ (prefixWord ++ tailWord_1437237).sum := by decide
  have hdescent : baseEnd_1437237 < baseStart_1437237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437265 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 6]
def baseStart_1437265 : Nat := 118140960795 + 1437265 * 2 ^ 59
def prefixEnd_1437265 : Nat := 4983230072969 + 3 ^ 40 * 1437265 * 2
def baseEnd_1437265 : Nat := 328003454615299745678953

theorem tailTrace_1437265 : CollatzResearch.WordTrace tailWord_1437265 prefixEnd_1437265 328003454615299745678953 := by
  unfold tailWord_1437265
  simp only [CollatzResearch.WordTrace]
  refine ⟨52421361138041845164617249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34947574092027896776411499 52421361138041845164617249)
  ·
    refine ⟨39316020853531383873462937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52421361138041845164617249 39316020853531383873462937)
    ·
      refine ⟨29487015640148537905097203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39316020853531383873462937 29487015640148537905097203)
      ·
        refine ⟨44230523460222806857645805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29487015640148537905097203 44230523460222806857645805)
        ·
          refine ⟨16586446297583552571617177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44230523460222806857645805 16586446297583552571617177)
          ·
            refine ⟨12439834723187664428712883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16586446297583552571617177 12439834723187664428712883)
            ·
              refine ⟨18659752084781496643069325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12439834723187664428712883 18659752084781496643069325)
              ·
                refine ⟨6997407031793061241150997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18659752084781496643069325 6997407031793061241150997)
                ·
                  refine ⟨328003454615299745678953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6997407031793061241150997 328003454615299745678953)
                  ·
                    rfl

theorem cell21_1437265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_1437265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437265 prefixEnd_1437265 := by exact prefixLift 1437265
  have htrace : WordTrace (prefixWord ++ tailWord_1437265) baseStart_1437265 baseEnd_1437265 := by
    simpa [prefixWord, tailWord_1437265, baseEnd_1437265] using wordTrace_append hprefix tailTrace_1437265
  have hstable : (prefixWord ++ tailWord_1437265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437265).length < 2 ^ (prefixWord ++ tailWord_1437265).sum := by decide
  have hdescent : baseEnd_1437265 < baseStart_1437265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437296 : List Nat := [2, 1, 1, 1, 6, 1, 2, 7]
def baseStart_1437296 : Nat := 118140960795 + 1437296 * 2 ^ 59
def prefixEnd_1437296 : Nat := 4983230072969 + 3 ^ 40 * 1437296 * 2
def baseEnd_1437296 : Nat := 109336843079216860220741

theorem tailTrace_1437296 : CollatzResearch.WordTrace tailWord_1437296 prefixEnd_1437296 109336843079216860220741 := by
  unfold tailWord_1437296
  simp only [CollatzResearch.WordTrace]
  refine ⟨26211245900464768729497871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34948327867286358305997161 26211245900464768729497871)
  ·
    refine ⟨39316868850697153094246807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26211245900464768729497871 39316868850697153094246807)
    ·
      refine ⟨58975303276045729641370211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39316868850697153094246807 58975303276045729641370211)
      ·
        refine ⟨88462954914068594462055317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58975303276045729641370211 88462954914068594462055317)
        ·
          refine ⟨4146701011596965365408843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88462954914068594462055317 4146701011596965365408843)
          ·
            refine ⟨6220051517395448048113265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4146701011596965365408843 6220051517395448048113265)
            ·
              refine ⟨4665038638046586036084949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6220051517395448048113265 4665038638046586036084949)
              ·
                refine ⟨109336843079216860220741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4665038638046586036084949 109336843079216860220741)
                ·
                  rfl

theorem cell21_1437296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_1437296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437296 prefixEnd_1437296 := by exact prefixLift 1437296
  have htrace : WordTrace (prefixWord ++ tailWord_1437296) baseStart_1437296 baseEnd_1437296 := by
    simpa [prefixWord, tailWord_1437296, baseEnd_1437296] using wordTrace_append hprefix tailTrace_1437296
  have hstable : (prefixWord ++ tailWord_1437296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437296).length < 2 ^ (prefixWord ++ tailWord_1437296).sum := by decide
  have hdescent : baseEnd_1437296 < baseStart_1437296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437330 : List Nat := [3, 2, 3, 1, 3, 2, 1, 6]
def baseStart_1437330 : Nat := 118140960795 + 1437330 * 2 ^ 59
def prefixEnd_1437330 : Nat := 4983230072969 + 3 ^ 40 * 1437330 * 2
def baseEnd_1437330 : Nat := 109339429500291359031829

theorem tailTrace_1437330 : CollatzResearch.WordTrace tailWord_1437330 prefixEnd_1437330 109339429500291359031829 := by
  unfold tailWord_1437330
  simp only [CollatzResearch.WordTrace]
  refine ⟨13105932970701590316433361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34949154588537574177155629 13105932970701590316433361)
  ·
    refine ⟨9829449728026192737325021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13105932970701590316433361 9829449728026192737325021)
    ·
      refine ⟨3686043648009822276496883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9829449728026192737325021 3686043648009822276496883)
      ·
        refine ⟨5529065472014733414745325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686043648009822276496883 5529065472014733414745325)
        ·
          refine ⟨2073399552005525030529497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5529065472014733414745325 2073399552005525030529497)
          ·
            refine ⟨1555049664004143772897123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2073399552005525030529497 1555049664004143772897123)
            ·
              refine ⟨2332574496006215659345685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555049664004143772897123 2332574496006215659345685)
              ·
                refine ⟨109339429500291359031829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2332574496006215659345685 109339429500291359031829)
                ·
                  rfl

theorem cell21_1437330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_1437330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437330 prefixEnd_1437330 := by exact prefixLift 1437330
  have htrace : WordTrace (prefixWord ++ tailWord_1437330) baseStart_1437330 baseEnd_1437330 := by
    simpa [prefixWord, tailWord_1437330, baseEnd_1437330] using wordTrace_append hprefix tailTrace_1437330
  have hstable : (prefixWord ++ tailWord_1437330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437330).length < 2 ^ (prefixWord ++ tailWord_1437330).sum := by decide
  have hdescent : baseEnd_1437330 < baseStart_1437330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437341 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1437341 : Nat := 118140960795 + 1437341 * 2 ^ 59
def prefixEnd_1437341 : Nat := 4983230072969 + 3 ^ 40 * 1437341 * 2
def baseEnd_1437341 : Nat := 328020798850740502412131

theorem tailTrace_1437341 : CollatzResearch.WordTrace tailWord_1437341 prefixEnd_1437341 328020798850740502412131 := by
  unfold tailWord_1437341
  simp only [CollatzResearch.WordTrace]
  refine ⟨52424133085766510144383877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34949422057177673429589251 52424133085766510144383877)
  ·
    refine ⟨9829524953581220652071977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52424133085766510144383877 9829524953581220652071977)
    ·
      refine ⟨7372143715185915489053983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9829524953581220652071977 7372143715185915489053983)
      ·
        refine ⟨11058215572778873233580975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7372143715185915489053983 11058215572778873233580975)
        ·
          refine ⟨16587323359168309850371463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11058215572778873233580975 16587323359168309850371463)
          ·
            refine ⟨24880985038752464775557195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16587323359168309850371463 24880985038752464775557195)
            ·
              refine ⟨37321477558128697163335793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24880985038752464775557195 37321477558128697163335793)
              ·
                refine ⟨27991108168596522872501845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37321477558128697163335793 27991108168596522872501845)
                ·
                  refine ⟨328020798850740502412131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27991108168596522872501845 328020798850740502412131)
                  ·
                    rfl

theorem cell21_1437341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1437341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437341 prefixEnd_1437341 := by exact prefixLift 1437341
  have htrace : WordTrace (prefixWord ++ tailWord_1437341) baseStart_1437341 baseEnd_1437341 := by
    simpa [prefixWord, tailWord_1437341, baseEnd_1437341] using wordTrace_append hprefix tailTrace_1437341
  have hstable : (prefixWord ++ tailWord_1437341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437341).length < 2 ^ (prefixWord ++ tailWord_1437341).sum := by decide
  have hdescent : baseEnd_1437341 < baseStart_1437341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437372 : List Nat := [2, 2, 2, 3, 1, 3, 8]
def baseStart_1437372 : Nat := 118140960795 + 1437372 * 2 ^ 59
def prefixEnd_1437372 : Nat := 4983230072969 + 3 ^ 40 * 1437372 * 2
def baseEnd_1437372 : Nat := 36447541497010148599489

theorem tailTrace_1437372 : CollatzResearch.WordTrace tailWord_1437372 prefixEnd_1437372 36447541497010148599489 := by
  unfold tailWord_1437372
  simp only [CollatzResearch.WordTrace]
  refine ⟨26212631874327101219381185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34950175832436134959174913 26212631874327101219381185)
  ·
    refine ⟨19659473905745325914535889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26212631874327101219381185 19659473905745325914535889)
    ·
      refine ⟨14744605429308994435901917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19659473905745325914535889 14744605429308994435901917)
      ·
        refine ⟨5529227035990872913463219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14744605429308994435901917 5529227035990872913463219)
        ·
          refine ⟨8293840553986309370194829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529227035990872913463219 8293840553986309370194829)
          ·
            refine ⟨3110190207744866013823061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8293840553986309370194829 3110190207744866013823061)
            ·
              refine ⟨36447541497010148599489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3110190207744866013823061 36447541497010148599489)
              ·
                rfl

theorem cell21_1437372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 8].length) (baseStart_1437372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437372 prefixEnd_1437372 := by exact prefixLift 1437372
  have htrace : WordTrace (prefixWord ++ tailWord_1437372) baseStart_1437372 baseEnd_1437372 := by
    simpa [prefixWord, tailWord_1437372, baseEnd_1437372] using wordTrace_append hprefix tailTrace_1437372
  have hstable : (prefixWord ++ tailWord_1437372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437372).length < 2 ^ (prefixWord ++ tailWord_1437372).sum := by decide
  have hdescent : baseEnd_1437372 < baseStart_1437372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437420 : List Nat := [2, 2, 1, 1, 2, 2, 5, 3, 3]
def baseStart_1437420 : Nat := 118140960795 + 1437420 * 2 ^ 59
def prefixEnd_1437420 : Nat := 4983230072969 + 3 ^ 40 * 1437420 * 2
def baseEnd_1437420 : Nat := 328038827727053920595303

theorem tailTrace_1437420 : CollatzResearch.WordTrace tailWord_1437420 prefixEnd_1437420 328038827727053920595303 := by
  unfold tailWord_1437420
  simp only [CollatzResearch.WordTrace]
  refine ⟨26213507226240153318254857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34951342968320204424339809 26213507226240153318254857)
  ·
    refine ⟨19660130419680114988691143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26213507226240153318254857 19660130419680114988691143)
    ·
      refine ⟨29490195629520172483036715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19660130419680114988691143 29490195629520172483036715)
      ·
        refine ⟨44235293444280258724555073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29490195629520172483036715 44235293444280258724555073)
        ·
          refine ⟨33176470083210194043416305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44235293444280258724555073 33176470083210194043416305)
          ·
            refine ⟨24882352562407645532562229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33176470083210194043416305 24882352562407645532562229)
            ·
              refine ⟨2332720552725716768677709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24882352562407645532562229 2332720552725716768677709)
              ·
                refine ⟨874770207272143788254141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2332720552725716768677709 874770207272143788254141)
                ·
                  refine ⟨328038827727053920595303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874770207272143788254141 328038827727053920595303)
                  ·
                    rfl

theorem cell21_1437420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_1437420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437420 prefixEnd_1437420 := by exact prefixLift 1437420
  have htrace : WordTrace (prefixWord ++ tailWord_1437420) baseStart_1437420 baseEnd_1437420 := by
    simpa [prefixWord, tailWord_1437420, baseEnd_1437420] using wordTrace_append hprefix tailTrace_1437420
  have hstable : (prefixWord ++ tailWord_1437420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437420).length < 2 ^ (prefixWord ++ tailWord_1437420).sum := by decide
  have hdescent : baseEnd_1437420 < baseStart_1437420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437431 : List Nat := [1, 1, 3, 1, 1, 1, 13]
def baseStart_1437431 : Nat := 118140960795 + 1437431 * 2 ^ 59
def prefixEnd_1437431 : Nat := 4983230072969 + 3 ^ 40 * 1437431 * 2
def baseEnd_1437431 : Nat := 36449037564102260656883

theorem tailTrace_1437431 : CollatzResearch.WordTrace tailWord_1437431 prefixEnd_1437431 36449037564102260656883 := by
  unfold tailWord_1437431
  simp only [CollatzResearch.WordTrace]
  refine ⟨52427415655440455515160147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34951610436960303676773431 52427415655440455515160147)
  ·
    refine ⟨78641123483160683272740221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52427415655440455515160147 78641123483160683272740221)
    ·
      refine ⟨29490421306185256227277583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78641123483160683272740221 29490421306185256227277583)
      ·
        refine ⟨44235631959277884340916375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29490421306185256227277583 44235631959277884340916375)
        ·
          refine ⟨66353447938916826511374563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44235631959277884340916375 66353447938916826511374563)
          ·
            refine ⟨99530171908375239767061845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66353447938916826511374563 99530171908375239767061845)
            ·
              refine ⟨36449037564102260656883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 99530171908375239767061845 36449037564102260656883)
              ·
                rfl

theorem cell21_1437431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 13].length) (baseStart_1437431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437431 prefixEnd_1437431 := by exact prefixLift 1437431
  have htrace : WordTrace (prefixWord ++ tailWord_1437431) baseStart_1437431 baseEnd_1437431 := by
    simpa [prefixWord, tailWord_1437431, baseEnd_1437431] using wordTrace_append hprefix tailTrace_1437431
  have hstable : (prefixWord ++ tailWord_1437431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437431).length < 2 ^ (prefixWord ++ tailWord_1437431).sum := by decide
  have hdescent : baseEnd_1437431 < baseStart_1437431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437448 : List Nat := [2, 1, 3, 2, 2, 1, 4, 6]
def baseStart_1437448 : Nat := 118140960795 + 1437448 * 2 ^ 59
def prefixEnd_1437448 : Nat := 4983230072969 + 3 ^ 40 * 1437448 * 2
def baseEnd_1437448 : Nat := 109348405902844031376193

theorem tailTrace_1437448 : CollatzResearch.WordTrace tailWord_1437448 prefixEnd_1437448 109348405902844031376193 := by
  unfold tailWord_1437448
  simp only [CollatzResearch.WordTrace]
  refine ⟨26214017848189433709264499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34952023797585911612352665 26214017848189433709264499)
  ·
    refine ⟨39321026772284150563896749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26214017848189433709264499 39321026772284150563896749)
    ·
      refine ⟨14745385039606556461461281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39321026772284150563896749 14745385039606556461461281)
      ·
        refine ⟨11059038779704917346095961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14745385039606556461461281 11059038779704917346095961)
        ·
          refine ⟨8294279084778688009571971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11059038779704917346095961 8294279084778688009571971)
          ·
            refine ⟨12441418627168032014357957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8294279084778688009571971 12441418627168032014357957)
            ·
              refine ⟨2332765992594006002692117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12441418627168032014357957 2332765992594006002692117)
              ·
                refine ⟨109348405902844031376193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2332765992594006002692117 109348405902844031376193)
                ·
                  rfl

theorem cell21_1437448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_1437448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437448 prefixEnd_1437448 := by exact prefixLift 1437448
  have htrace : WordTrace (prefixWord ++ tailWord_1437448) baseStart_1437448 baseEnd_1437448 := by
    simpa [prefixWord, tailWord_1437448, baseEnd_1437448] using wordTrace_append hprefix tailTrace_1437448
  have hstable : (prefixWord ++ tailWord_1437448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437448).length < 2 ^ (prefixWord ++ tailWord_1437448).sum := by decide
  have hdescent : baseEnd_1437448 < baseStart_1437448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437496 : List Nat := [2, 1, 2, 1, 3, 4, 1, 4, 3]
def baseStart_1437496 : Nat := 118140960795 + 1437496 * 2 ^ 59
def prefixEnd_1437496 : Nat := 4983230072969 + 3 ^ 40 * 1437496 * 2
def baseEnd_1437496 : Nat := 328056171962494677328481

theorem tailTrace_1437496 : CollatzResearch.WordTrace tailWord_1437496 prefixEnd_1437496 328056171962494677328481 := by
  unfold tailWord_1437496
  simp only [CollatzResearch.WordTrace]
  refine ⟨26214893200102485808138171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34953190933469981077517561 26214893200102485808138171)
  ·
    refine ⟨39322339800153728712207257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26214893200102485808138171 39322339800153728712207257)
    ·
      refine ⟨29491754850115296534155443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39322339800153728712207257 29491754850115296534155443)
      ·
        refine ⟨44237632275172944801233165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29491754850115296534155443 44237632275172944801233165)
        ·
          refine ⟨16589112103189854300462437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44237632275172944801233165 16589112103189854300462437)
          ·
            refine ⟨3110458519348097681336707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16589112103189854300462437 3110458519348097681336707)
            ·
              refine ⟨4665687779022146522005061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110458519348097681336707 4665687779022146522005061)
              ·
                refine ⟨874816458566652472875949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4665687779022146522005061 874816458566652472875949)
                ·
                  refine ⟨328056171962494677328481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874816458566652472875949 328056171962494677328481)
                  ·
                    rfl

theorem cell21_1437496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 3].length) (baseStart_1437496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437496 prefixEnd_1437496 := by exact prefixLift 1437496
  have htrace : WordTrace (prefixWord ++ tailWord_1437496) baseStart_1437496 baseEnd_1437496 := by
    simpa [prefixWord, tailWord_1437496, baseEnd_1437496] using wordTrace_append hprefix tailTrace_1437496
  have hstable : (prefixWord ++ tailWord_1437496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437496).length < 2 ^ (prefixWord ++ tailWord_1437496).sum := by decide
  have hdescent : baseEnd_1437496 < baseStart_1437496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437586 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_1437586 : Nat := 118140960795 + 1437586 * 2 ^ 59
def prefixEnd_1437586 : Nat := 4983230072969 + 3 ^ 40 * 1437586 * 2
def baseEnd_1437586 : Nat := 328076711188674520828297

theorem tailTrace_1437586 : CollatzResearch.WordTrace tailWord_1437586 prefixEnd_1437586 328076711188674520828297 := by
  unfold tailWord_1437586
  simp only [CollatzResearch.WordTrace]
  refine ⟨13108267242469729246763153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34955379313252611324701741 13108267242469729246763153)
  ·
    refine ⟨9831200431852296935072365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13108267242469729246763153 9831200431852296935072365)
    ·
      refine ⟨3686700161944611350652137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9831200431852296935072365 3686700161944611350652137)
      ·
        refine ⟨2765025121458458512989103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3686700161944611350652137 2765025121458458512989103)
        ·
          refine ⟨4147537682187687769483655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2765025121458458512989103 4147537682187687769483655)
          ·
            refine ⟨6221306523281531654225483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147537682187687769483655 6221306523281531654225483)
            ·
              refine ⟨9331959784922297481338225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6221306523281531654225483 9331959784922297481338225)
              ·
                refine ⟨6998969838691723111003669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9331959784922297481338225 6998969838691723111003669)
                ·
                  refine ⟨328076711188674520828297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6998969838691723111003669 328076711188674520828297)
                  ·
                    rfl

theorem cell21_1437586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_1437586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437586 prefixEnd_1437586 := by exact prefixLift 1437586
  have htrace : WordTrace (prefixWord ++ tailWord_1437586) baseStart_1437586 baseEnd_1437586 := by
    simpa [prefixWord, tailWord_1437586, baseEnd_1437586] using wordTrace_append hprefix tailTrace_1437586
  have hstable : (prefixWord ++ tailWord_1437586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437586).length < 2 ^ (prefixWord ++ tailWord_1437586).sum := by decide
  have hdescent : baseEnd_1437586 < baseStart_1437586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437620 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1437620 : Nat := 118140960795 + 1437620 * 2 ^ 59
def prefixEnd_1437620 : Nat := 4983230072969 + 3 ^ 40 * 1437620 * 2
def baseEnd_1437620 : Nat := 328084470451898017261561

theorem tailTrace_1437620 : CollatzResearch.WordTrace tailWord_1437620 prefixEnd_1437620 328084470451898017261561 := by
  unfold tailWord_1437620
  simp only [CollatzResearch.WordTrace]
  refine ⟨26217154525877870396895157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34956206034503827195860209 26217154525877870396895157)
  ·
    refine ⟨2457858236801050349708921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26217154525877870396895157 2457858236801050349708921)
    ·
      refine ⟨1843393677600787762281691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2457858236801050349708921 1843393677600787762281691)
      ·
        refine ⟨2765090516401181643422537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843393677600787762281691 2765090516401181643422537)
        ·
          refine ⟨2073817887300886232566903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2765090516401181643422537 2073817887300886232566903)
          ·
            refine ⟨3110726830951329348850355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073817887300886232566903 3110726830951329348850355)
            ·
              refine ⟨4666090246426994023275533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110726830951329348850355 4666090246426994023275533)
              ·
                refine ⟨1749783842410122758728325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4666090246426994023275533 1749783842410122758728325)
                ·
                  refine ⟨328084470451898017261561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749783842410122758728325 328084470451898017261561)
                  ·
                    rfl

theorem cell21_1437620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1437620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437620 prefixEnd_1437620 := by exact prefixLift 1437620
  have htrace : WordTrace (prefixWord ++ tailWord_1437620) baseStart_1437620 baseEnd_1437620 := by
    simpa [prefixWord, tailWord_1437620, baseEnd_1437620] using wordTrace_append hprefix tailTrace_1437620
  have hstable : (prefixWord ++ tailWord_1437620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437620).length < 2 ^ (prefixWord ++ tailWord_1437620).sum := by decide
  have hdescent : baseEnd_1437620 < baseStart_1437620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437724 : List Nat := [2, 2, 3, 1, 3, 1, 2, 4, 3]
def baseStart_1437724 : Nat := 118140960795 + 1437724 * 2 ^ 59
def prefixEnd_1437724 : Nat := 4983230072969 + 3 ^ 40 * 1437724 * 2
def baseEnd_1437724 : Nat := 328108204668816947528015

theorem tailTrace_1437724 : CollatzResearch.WordTrace tailWord_1437724 prefixEnd_1437724 328108204668816947528015 := by
  unfold tailWord_1437724
  simp only [CollatzResearch.WordTrace]
  refine ⟨26219051121689483277788113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34958734828919311037050817 26219051121689483277788113)
  ·
    refine ⟨19664288341267112458341085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26219051121689483277788113 19664288341267112458341085)
    ·
      refine ⟨7374108127975167171877907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19664288341267112458341085 7374108127975167171877907)
      ·
        refine ⟨11061162191962750757816861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7374108127975167171877907 11061162191962750757816861)
        ·
          refine ⟨4147935821986031534181323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11061162191962750757816861 4147935821986031534181323)
          ·
            refine ⟨6221903732979047301271985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147935821986031534181323 6221903732979047301271985)
            ·
              refine ⟨4666427799734285475953989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6221903732979047301271985 4666427799734285475953989)
              ·
                refine ⟨874955212450178526741373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4666427799734285475953989 874955212450178526741373)
                ·
                  refine ⟨328108204668816947528015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874955212450178526741373 328108204668816947528015)
                  ·
                    rfl

theorem cell21_1437724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_1437724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437724 prefixEnd_1437724 := by exact prefixLift 1437724
  have htrace : WordTrace (prefixWord ++ tailWord_1437724) baseStart_1437724 baseEnd_1437724 := by
    simpa [prefixWord, tailWord_1437724, baseEnd_1437724] using wordTrace_append hprefix tailTrace_1437724
  have hstable : (prefixWord ++ tailWord_1437724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437724).length < 2 ^ (prefixWord ++ tailWord_1437724).sum := by decide
  have hdescent : baseEnd_1437724 < baseStart_1437724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437752 : List Nat := [2, 1, 2, 1, 6, 1, 1, 7]
def baseStart_1437752 : Nat := 118140960795 + 1437752 * 2 ^ 59
def prefixEnd_1437752 : Nat := 4983230072969 + 3 ^ 40 * 1437752 * 2
def baseEnd_1437752 : Nat := 109371531550098373687097

theorem tailTrace_1437752 : CollatzResearch.WordTrace tailWord_1437752 prefixEnd_1437752 109371531550098373687097 := by
  unfold tailWord_1437752
  simp only [CollatzResearch.WordTrace]
  refine ⟨26219561743638763668797755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34959415658185018225063673 26219561743638763668797755)
  ·
    refine ⟨39329342615458145503196633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26219561743638763668797755 39329342615458145503196633)
    ·
      refine ⟨29497006961593609127397475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39329342615458145503196633 29497006961593609127397475)
      ·
        refine ⟨44245510442390413691096213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29497006961593609127397475 44245510442390413691096213)
        ·
          refine ⟨2074008301987050641770135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44245510442390413691096213 2074008301987050641770135)
          ·
            refine ⟨3111012452980575962655203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074008301987050641770135 3111012452980575962655203)
            ·
              refine ⟨4666518679470863943982805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3111012452980575962655203 4666518679470863943982805)
              ·
                refine ⟨109371531550098373687097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4666518679470863943982805 109371531550098373687097)
                ·
                  rfl

theorem cell21_1437752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_1437752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437752 prefixEnd_1437752 := by exact prefixLift 1437752
  have htrace : WordTrace (prefixWord ++ tailWord_1437752) baseStart_1437752 baseEnd_1437752 := by
    simpa [prefixWord, tailWord_1437752, baseEnd_1437752] using wordTrace_append hprefix tailTrace_1437752
  have hstable : (prefixWord ++ tailWord_1437752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437752).length < 2 ^ (prefixWord ++ tailWord_1437752).sum := by decide
  have hdescent : baseEnd_1437752 < baseStart_1437752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437758 : List Nat := [4, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_1437758 : Nat := 118140960795 + 1437758 * 2 ^ 59
def prefixEnd_1437758 : Nat := 4983230072969 + 3 ^ 40 * 1437758 * 2
def baseEnd_1437758 : Nat := 328115963932040443961279

theorem tailTrace_1437758 : CollatzResearch.WordTrace tailWord_1437758 prefixEnd_1437758 328115963932040443961279 := by
  unfold tailWord_1437758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6554917790656973795289241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34959561550170526908209285 6554917790656973795289241)
  ·
    refine ⟨4916188342992730346466931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6554917790656973795289241 4916188342992730346466931)
    ·
      refine ⟨7374282514489095519700397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4916188342992730346466931 7374282514489095519700397)
      ·
        refine ⟨2765355942933410819887649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7374282514489095519700397 2765355942933410819887649)
        ·
          refine ⟨2074016957200058114915737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2765355942933410819887649 2074016957200058114915737)
          ·
            refine ⟨1555512717900043586186803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2074016957200058114915737 1555512717900043586186803)
            ·
              refine ⟨2333269076850065379280205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555512717900043586186803 2333269076850065379280205)
              ·
                refine ⟨874975903818774517230077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2333269076850065379280205 874975903818774517230077)
                ·
                  refine ⟨328115963932040443961279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874975903818774517230077 328115963932040443961279)
                  ·
                    rfl

theorem cell21_1437758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_1437758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437758 prefixEnd_1437758 := by exact prefixLift 1437758
  have htrace : WordTrace (prefixWord ++ tailWord_1437758) baseStart_1437758 baseEnd_1437758 := by
    simpa [prefixWord, tailWord_1437758, baseEnd_1437758] using wordTrace_append hprefix tailTrace_1437758
  have hstable : (prefixWord ++ tailWord_1437758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437758).length < 2 ^ (prefixWord ++ tailWord_1437758).sum := by decide
  have hdescent : baseEnd_1437758 < baseStart_1437758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437783 : List Nat := [1, 1, 3, 2, 2, 1, 2, 6, 3]
def baseStart_1437783 : Nat := 118140960795 + 1437783 * 2 ^ 59
def prefixEnd_1437783 : Nat := 4983230072969 + 3 ^ 40 * 1437783 * 2
def baseEnd_1437783 : Nat := 328121669272645956044561

theorem tailTrace_1437783 : CollatzResearch.WordTrace tailWord_1437783 prefixEnd_1437783 328121669272645956044561 := by
  unfold tailWord_1437783
  simp only [CollatzResearch.WordTrace]
  refine ⟨52440254150165219631974003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34960169433443479754649335 52440254150165219631974003)
  ·
    refine ⟨78660381225247829447961005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52440254150165219631974003 78660381225247829447961005)
    ·
      refine ⟨29497642959467936042985377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78660381225247829447961005 29497642959467936042985377)
      ·
        refine ⟨22123232219600952032239033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29497642959467936042985377 22123232219600952032239033)
        ·
          refine ⟨16592424164700714024179275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22123232219600952032239033 16592424164700714024179275)
          ·
            refine ⟨24888636247051071036268913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16592424164700714024179275 24888636247051071036268913)
            ·
              refine ⟨18666477185288303277201685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24888636247051071036268913 18666477185288303277201685)
              ·
                refine ⟨874991118060389216118829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18666477185288303277201685 874991118060389216118829)
                ·
                  refine ⟨328121669272645956044561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874991118060389216118829 328121669272645956044561)
                  ·
                    rfl

theorem cell21_1437783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 3].length) (baseStart_1437783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437783 prefixEnd_1437783 := by exact prefixLift 1437783
  have htrace : WordTrace (prefixWord ++ tailWord_1437783) baseStart_1437783 baseEnd_1437783 := by
    simpa [prefixWord, tailWord_1437783, baseEnd_1437783] using wordTrace_append hprefix tailTrace_1437783
  have hstable : (prefixWord ++ tailWord_1437783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437783).length < 2 ^ (prefixWord ++ tailWord_1437783).sum := by decide
  have hdescent : baseEnd_1437783 < baseStart_1437783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437932 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_1437932 : Nat := 118140960795 + 1437932 * 2 ^ 59
def prefixEnd_1437932 : Nat := 4983230072969 + 3 ^ 40 * 1437932 * 2
def baseEnd_1437932 : Nat := 328155673102654808060923

theorem tailTrace_1437932 : CollatzResearch.WordTrace tailWord_1437932 prefixEnd_1437932 328155673102654808060923 := by
  unfold tailWord_1437932
  simp only [CollatzResearch.WordTrace]
  refine ⟨26222844313312709039574025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34963792417750278719432033 26222844313312709039574025)
  ·
    refine ⟨19667133234984531779680519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26222844313312709039574025 19667133234984531779680519)
    ·
      refine ⟨29500699852476797669520779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19667133234984531779680519 29500699852476797669520779)
      ·
        refine ⟨44251049778715196504281169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29500699852476797669520779 44251049778715196504281169)
        ·
          refine ⟨33188287334036397378210877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44251049778715196504281169 33188287334036397378210877)
          ·
            refine ⟨12445607750263649016829079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33188287334036397378210877 12445607750263649016829079)
            ·
              refine ⟨18668411625395473525243619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12445607750263649016829079 18668411625395473525243619)
              ·
                refine ⟨28002617438093210287865429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18668411625395473525243619 28002617438093210287865429)
                ·
                  refine ⟨328155673102654808060923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28002617438093210287865429 328155673102654808060923)
                  ·
                    rfl

theorem cell21_1437932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_1437932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437932 prefixEnd_1437932 := by exact prefixLift 1437932
  have htrace : WordTrace (prefixWord ++ tailWord_1437932) baseStart_1437932 baseEnd_1437932 := by
    simpa [prefixWord, tailWord_1437932, baseEnd_1437932] using wordTrace_append hprefix tailTrace_1437932
  have hstable : (prefixWord ++ tailWord_1437932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437932).length < 2 ^ (prefixWord ++ tailWord_1437932).sum := by decide
  have hdescent : baseEnd_1437932 < baseStart_1437932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437963 : List Nat := [1, 1, 1, 1, 5, 2, 4, 6]
def baseStart_1437963 : Nat := 118140960795 + 1437963 * 2 ^ 59
def prefixEnd_1437963 : Nat := 4983230072969 + 3 ^ 40 * 1437963 * 2
def baseEnd_1437963 : Nat := 109387582575001881014731

theorem tailTrace_1437963 : CollatzResearch.WordTrace tailWord_1437963 prefixEnd_1437963 109387582575001881014731 := by
  unfold tailWord_1437963
  simp only [CollatzResearch.WordTrace]
  refine ⟨52446819289513110373526543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34964546193008740249017695 52446819289513110373526543)
  ·
    refine ⟨78670228934269665560289815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52446819289513110373526543 78670228934269665560289815)
    ·
      refine ⟨118005343401404498340434723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78670228934269665560289815 118005343401404498340434723)
      ·
        refine ⟨177008015102106747510652085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118005343401404498340434723 177008015102106747510652085)
        ·
          refine ⟨16594501415822507579123633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177008015102106747510652085 16594501415822507579123633)
          ·
            refine ⟨12445876061866880684342725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16594501415822507579123633 12445876061866880684342725)
            ·
              refine ⟨2333601761600040128314261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12445876061866880684342725 2333601761600040128314261)
              ·
                refine ⟨109387582575001881014731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2333601761600040128314261 109387582575001881014731)
                ·
                  rfl

theorem cell21_1437963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 6].length) (baseStart_1437963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437963 prefixEnd_1437963 := by exact prefixLift 1437963
  have htrace : WordTrace (prefixWord ++ tailWord_1437963) baseStart_1437963 baseEnd_1437963 := by
    simpa [prefixWord, tailWord_1437963, baseEnd_1437963] using wordTrace_append hprefix tailTrace_1437963
  have hstable : (prefixWord ++ tailWord_1437963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437963).length < 2 ^ (prefixWord ++ tailWord_1437963).sum := by decide
  have hdescent : baseEnd_1437963 < baseStart_1437963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437997 : List Nat := [1, 5, 3, 1, 3, 8]
def baseStart_1437997 : Nat := 118140960795 + 1437997 * 2 ^ 59
def prefixEnd_1437997 : Nat := 4983230072969 + 3 ^ 40 * 1437997 * 2
def baseEnd_1437997 : Nat := 12154463221786264425091

theorem tailTrace_1437997 : CollatzResearch.WordTrace tailWord_1437997 prefixEnd_1437997 12154463221786264425091 := by
  unfold tailWord_1437997
  simp only [CollatzResearch.WordTrace]
  refine ⟨52448059371389934180264245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34965372914259956120176163 52448059371389934180264245)
  ·
    refine ⟨4917005566067806329399773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52448059371389934180264245 4917005566067806329399773)
    ·
      refine ⟨1843877087275427373524915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4917005566067806329399773 1843877087275427373524915)
      ·
        refine ⟨2765815630913141060287373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843877087275427373524915 2765815630913141060287373)
        ·
          refine ⟨1037180861592427897607765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2765815630913141060287373 1037180861592427897607765)
          ·
            refine ⟨12154463221786264425091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1037180861592427897607765 12154463221786264425091)
            ·
              rfl

theorem cell21_1437997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 8].length) (baseStart_1437997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1437997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1437997 prefixEnd_1437997 := by exact prefixLift 1437997
  have htrace : WordTrace (prefixWord ++ tailWord_1437997) baseStart_1437997 baseEnd_1437997 := by
    simpa [prefixWord, tailWord_1437997, baseEnd_1437997] using wordTrace_append hprefix tailTrace_1437997
  have hstable : (prefixWord ++ tailWord_1437997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437997).length < 2 ^ (prefixWord ++ tailWord_1437997).sum := by decide
  have hdescent : baseEnd_1437997 < baseStart_1437997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438008 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_1438008 : Nat := 118140960795 + 1438008 * 2 ^ 59
def prefixEnd_1438008 : Nat := 4983230072969 + 3 ^ 40 * 1438008 * 2
def baseEnd_1438008 : Nat := 328173017338095564794101

theorem tailTrace_1438008 : CollatzResearch.WordTrace tailWord_1438008 prefixEnd_1438008 328173017338095564794101 := by
  unfold tailWord_1438008
  simp only [CollatzResearch.WordTrace]
  refine ⟨26224230287175041529457339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34965640382900055372609785 26224230287175041529457339)
  ·
    refine ⟨39336345430762562294186009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26224230287175041529457339 39336345430762562294186009)
    ·
      refine ⟨29502259073071921720639507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39336345430762562294186009 29502259073071921720639507)
      ·
        refine ⟨44253388609607882580959261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29502259073071921720639507 44253388609607882580959261)
        ·
          refine ⟨16595020728602955967859723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44253388609607882580959261 16595020728602955967859723)
          ·
            refine ⟨24892531092904433951789585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16595020728602955967859723 24892531092904433951789585)
            ·
              refine ⟨18669398319678325463842189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24892531092904433951789585 18669398319678325463842189)
              ·
                refine ⟨7001024369879372048940821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18669398319678325463842189 7001024369879372048940821)
                ·
                  refine ⟨328173017338095564794101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7001024369879372048940821 328173017338095564794101)
                  ·
                    rfl

theorem cell21_1438008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_1438008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438008 prefixEnd_1438008 := by exact prefixLift 1438008
  have htrace : WordTrace (prefixWord ++ tailWord_1438008) baseStart_1438008 baseEnd_1438008 := by
    simpa [prefixWord, tailWord_1438008, baseEnd_1438008] using wordTrace_append hprefix tailTrace_1438008
  have hstable : (prefixWord ++ tailWord_1438008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438008).length < 2 ^ (prefixWord ++ tailWord_1438008).sum := by decide
  have hdescent : baseEnd_1438008 < baseStart_1438008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438090 : List Nat := [3, 1, 2, 5, 1, 2, 2, 5]
def baseStart_1438090 : Nat := 118140960795 + 1438090 * 2 ^ 59
def prefixEnd_1438090 : Nat := 4983230072969 + 3 ^ 40 * 1438090 * 2
def baseEnd_1438090 : Nat := 109397243618427214809089

theorem tailTrace_1438090 : CollatzResearch.WordTrace tailWord_1438090 prefixEnd_1438090 109397243618427214809089 := by
  unfold tailWord_1438090
  simp only [CollatzResearch.WordTrace]
  refine ⟨13112862840013252765849931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34967634240035340708933149 13112862840013252765849931)
  ·
    refine ⟨19669294260019879148774897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13112862840013252765849931 19669294260019879148774897)
    ·
      refine ⟨14751970695014909361581173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19669294260019879148774897 14751970695014909361581173)
      ·
        refine ⟨1382997252657647752648235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14751970695014909361581173 1382997252657647752648235)
        ·
          refine ⟨2074495878986471628972353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1382997252657647752648235 2074495878986471628972353)
          ·
            refine ⟨1555871909239853721729265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2074495878986471628972353 1555871909239853721729265)
            ·
              refine ⟨1166903931929890291296949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1555871909239853721729265 1166903931929890291296949)
              ·
                refine ⟨109397243618427214809089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1166903931929890291296949 109397243618427214809089)
                ·
                  rfl

theorem cell21_1438090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_1438090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438090 prefixEnd_1438090 := by exact prefixLift 1438090
  have htrace : WordTrace (prefixWord ++ tailWord_1438090) baseStart_1438090 baseEnd_1438090 := by
    simpa [prefixWord, tailWord_1438090, baseEnd_1438090] using wordTrace_append hprefix tailTrace_1438090
  have hstable : (prefixWord ++ tailWord_1438090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438090).length < 2 ^ (prefixWord ++ tailWord_1438090).sum := by decide
  have hdescent : baseEnd_1438090 < baseStart_1438090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438104 : List Nat := [2, 1, 2, 5, 1, 1, 3, 3, 3]
def baseStart_1438104 : Nat := 118140960795 + 1438104 * 2 ^ 59
def prefixEnd_1438104 : Nat := 4983230072969 + 3 ^ 40 * 1438104 * 2
def baseEnd_1438104 : Nat := 328194925846020731193905

theorem tailTrace_1438104 : CollatzResearch.WordTrace tailWord_1438104 prefixEnd_1438104 328194925846020731193905 := by
  unfold tailWord_1438104
  simp only [CollatzResearch.WordTrace]
  refine ⟨26225980991001145727204683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34967974654668194302939577 26225980991001145727204683)
  ·
    refine ⟨39338971486501718590807025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26225980991001145727204683 39338971486501718590807025)
    ·
      refine ⟨29504228614876288943105269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39338971486501718590807025 29504228614876288943105269)
      ·
        refine ⟨2766021432644652088416119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29504228614876288943105269 2766021432644652088416119)
        ·
          refine ⟨4149032148966978132624179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2766021432644652088416119 4149032148966978132624179)
          ·
            refine ⟨6223548223450467198936269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4149032148966978132624179 6223548223450467198936269)
            ·
              refine ⟨2333830583793925199601101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6223548223450467198936269 2333830583793925199601101)
              ·
                refine ⟨875186468922721949850413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2333830583793925199601101 875186468922721949850413)
                ·
                  refine ⟨328194925846020731193905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875186468922721949850413 328194925846020731193905)
                  ·
                    rfl

theorem cell21_1438104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 3].length) (baseStart_1438104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438104 prefixEnd_1438104 := by exact prefixLift 1438104
  have htrace : WordTrace (prefixWord ++ tailWord_1438104) baseStart_1438104 baseEnd_1438104 := by
    simpa [prefixWord, tailWord_1438104, baseEnd_1438104] using wordTrace_append hprefix tailTrace_1438104
  have hstable : (prefixWord ++ tailWord_1438104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438104).length < 2 ^ (prefixWord ++ tailWord_1438104).sum := by decide
  have hdescent : baseEnd_1438104 < baseStart_1438104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438115 : List Nat := [1, 1, 1, 4, 1, 6, 7]
def baseStart_1438115 : Nat := 118140960795 + 1438115 * 2 ^ 59
def prefixEnd_1438115 : Nat := 4983230072969 + 3 ^ 40 * 1438115 * 2
def baseEnd_1438115 : Nat := 36466381799543017390061

theorem tailTrace_1438115 : CollatzResearch.WordTrace tailWord_1438115 prefixEnd_1438115 36466381799543017390061 := by
  unfold tailWord_1438115
  simp only [CollatzResearch.WordTrace]
  refine ⟨52452363184962440333059799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34968242123308293555373199 52452363184962440333059799)
  ·
    refine ⟨78678544777443660499589699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52452363184962440333059799 78678544777443660499589699)
    ·
      refine ⟨118017817166165490749384549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78678544777443660499589699 118017817166165490749384549)
      ·
        refine ⟨22128340718656029515509603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118017817166165490749384549 22128340718656029515509603)
        ·
          refine ⟨33192511077984044273264405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22128340718656029515509603 33192511077984044273264405)
          ·
            refine ⟨1555898956780502075309269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33192511077984044273264405 1555898956780502075309269)
            ·
              refine ⟨36466381799543017390061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1555898956780502075309269 36466381799543017390061)
              ·
                rfl

theorem cell21_1438115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 7].length) (baseStart_1438115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438115 prefixEnd_1438115 := by exact prefixLift 1438115
  have htrace : WordTrace (prefixWord ++ tailWord_1438115) baseStart_1438115 baseEnd_1438115 := by
    simpa [prefixWord, tailWord_1438115, baseEnd_1438115] using wordTrace_append hprefix tailTrace_1438115
  have hstable : (prefixWord ++ tailWord_1438115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438115).length < 2 ^ (prefixWord ++ tailWord_1438115).sum := by decide
  have hdescent : baseEnd_1438115 < baseStart_1438115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438177 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 4]
def baseStart_1438177 : Nat := 118140960795 + 1438177 * 2 ^ 59
def prefixEnd_1438177 : Nat := 4983230072969 + 3 ^ 40 * 1438177 * 2
def baseEnd_1438177 : Nat := 328211585440588826477089

theorem tailTrace_1438177 : CollatzResearch.WordTrace tailWord_1438177 prefixEnd_1438177 328211585440588826477089 := by
  unfold tailWord_1438177
  simp only [CollatzResearch.WordTrace]
  refine ⟨52454624510737824921816785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34969749673825216614544523 52454624510737824921816785)
  ·
    refine ⟨39340968383053368691362589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52454624510737824921816785 39340968383053368691362589)
    ·
      refine ⟨14752863143645013259260971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39340968383053368691362589 14752863143645013259260971)
      ·
        refine ⟨22129294715467519888891457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14752863143645013259260971 22129294715467519888891457)
        ·
          refine ⟨16596971036600639916668593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22129294715467519888891457 16596971036600639916668593)
          ·
            refine ⟨12447728277450479937501445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16596971036600639916668593 12447728277450479937501445)
            ·
              refine ⟨2333949052021964988281521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12447728277450479937501445 2333949052021964988281521)
              ·
                refine ⟨1750461789016473741211141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2333949052021964988281521 1750461789016473741211141)
                ·
                  refine ⟨328211585440588826477089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1750461789016473741211141 328211585440588826477089)
                  ·
                    rfl

theorem cell21_1438177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_1438177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438177 prefixEnd_1438177 := by exact prefixLift 1438177
  have htrace : WordTrace (prefixWord ++ tailWord_1438177) baseStart_1438177 baseEnd_1438177 := by
    simpa [prefixWord, tailWord_1438177, baseEnd_1438177] using wordTrace_append hprefix tailTrace_1438177
  have hstable : (prefixWord ++ tailWord_1438177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438177).length < 2 ^ (prefixWord ++ tailWord_1438177).sum := by decide
  have hdescent : baseEnd_1438177 < baseStart_1438177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438214 : List Nat := [6, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1438214 : Nat := 118140960795 + 1438214 * 2 ^ 59
def prefixEnd_1438214 : Nat := 4983230072969 + 3 ^ 40 * 1438214 * 2
def baseEnd_1438214 : Nat := 328220029344684984360347

theorem tailTrace_1438214 : CollatzResearch.WordTrace tailWord_1438214 prefixEnd_1438214 328220029344684984360347 := by
  unfold tailWord_1438214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639249187862618132528553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34970649341069186827275797 1639249187862618132528553)
  ·
    refine ⟨1229436890896963599396415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1639249187862618132528553 1229436890896963599396415)
    ·
      refine ⟨1844155336345445399094623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1229436890896963599396415 1844155336345445399094623)
      ·
        refine ⟨2766233004518168098641935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844155336345445399094623 2766233004518168098641935)
        ·
          refine ⟨4149349506777252147962903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2766233004518168098641935 4149349506777252147962903)
          ·
            refine ⟨6224024260165878221944355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4149349506777252147962903 6224024260165878221944355)
            ·
              refine ⟨9336036390248817332916533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6224024260165878221944355 9336036390248817332916533)
              ·
                refine ⟨875253411585826624960925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9336036390248817332916533 875253411585826624960925)
                ·
                  refine ⟨328220029344684984360347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875253411585826624960925 328220029344684984360347)
                  ·
                    rfl

theorem cell21_1438214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1438214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438214 prefixEnd_1438214 := by exact prefixLift 1438214
  have htrace : WordTrace (prefixWord ++ tailWord_1438214) baseStart_1438214 baseEnd_1438214 := by
    simpa [prefixWord, tailWord_1438214, baseEnd_1438214] using wordTrace_append hprefix tailTrace_1438214
  have hstable : (prefixWord ++ tailWord_1438214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438214).length < 2 ^ (prefixWord ++ tailWord_1438214).sum := by decide
  have hdescent : baseEnd_1438214 < baseStart_1438214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438346 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_1438346 : Nat := 118140960795 + 1438346 * 2 ^ 59
def prefixEnd_1438346 : Nat := 4983230072969 + 3 ^ 40 * 1438346 * 2
def baseEnd_1438346 : Nat := 328250153543082088160077

theorem tailTrace_1438346 : CollatzResearch.WordTrace tailWord_1438346 prefixEnd_1438346 328250153543082088160077 := by
  unfold tailWord_1438346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13115197111781391696179723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34973858964750377856479261 13115197111781391696179723)
  ·
    refine ⟨19672795667672087544269585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13115197111781391696179723 19672795667672087544269585)
    ·
      refine ⟨14754596750754065658202189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19672795667672087544269585 14754596750754065658202189)
      ·
        refine ⟨5532973781532774621825821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14754596750754065658202189 5532973781532774621825821)
        ·
          refine ⟨2074865168074790483184683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5532973781532774621825821 2074865168074790483184683)
          ·
            refine ⟨3112297752112185724777025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074865168074790483184683 3112297752112185724777025)
            ·
              refine ⟨2334223314084139293582769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3112297752112185724777025 2334223314084139293582769)
              ·
                refine ⟨1750667485563104470187077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2334223314084139293582769 1750667485563104470187077)
                ·
                  refine ⟨328250153543082088160077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1750667485563104470187077 328250153543082088160077)
                  ·
                    rfl

theorem cell21_1438346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_1438346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438346 prefixEnd_1438346 := by exact prefixLift 1438346
  have htrace : WordTrace (prefixWord ++ tailWord_1438346) baseStart_1438346 baseEnd_1438346 := by
    simpa [prefixWord, tailWord_1438346, baseEnd_1438346] using wordTrace_append hprefix tailTrace_1438346
  have hstable : (prefixWord ++ tailWord_1438346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438346).length < 2 ^ (prefixWord ++ tailWord_1438346).sum := by decide
  have hdescent : baseEnd_1438346 < baseStart_1438346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438436 : List Nat := [2, 3, 1, 1, 1, 6, 2, 5]
def baseStart_1438436 : Nat := 118140960795 + 1438436 * 2 ^ 59
def prefixEnd_1438436 : Nat := 4983230072969 + 3 ^ 40 * 1438436 * 2
def baseEnd_1438436 : Nat := 109423564256420643886631

theorem tailTrace_1438436 : CollatzResearch.WordTrace tailWord_1438436 prefixEnd_1438436 109423564256420643886631 := by
  unfold tailWord_1438436
  simp only [CollatzResearch.WordTrace]
  refine ⟨26232035508399756077747581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34976047344533008103663441 26232035508399756077747581)
  ·
    refine ⟨9837013315649908529155343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26232035508399756077747581 9837013315649908529155343)
    ·
      refine ⟨14755519973474862793733015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9837013315649908529155343 14755519973474862793733015)
      ·
        refine ⟨22133279960212294190599523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14755519973474862793733015 22133279960212294190599523)
        ·
          refine ⟨33199919940318441285899285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22133279960212294190599523 33199919940318441285899285)
          ·
            refine ⟨1556246247202426935276529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33199919940318441285899285 1556246247202426935276529)
            ·
              refine ⟨1167184685401820201457397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1556246247202426935276529 1167184685401820201457397)
              ·
                refine ⟨109423564256420643886631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1167184685401820201457397 109423564256420643886631)
                ·
                  rfl

theorem cell21_1438436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_1438436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438436 prefixEnd_1438436 := by exact prefixLift 1438436
  have htrace : WordTrace (prefixWord ++ tailWord_1438436) baseStart_1438436 baseEnd_1438436 := by
    simpa [prefixWord, tailWord_1438436, baseEnd_1438436] using wordTrace_append hprefix tailTrace_1438436
  have hstable : (prefixWord ++ tailWord_1438436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438436).length < 2 ^ (prefixWord ++ tailWord_1438436).sum := by decide
  have hdescent : baseEnd_1438436 < baseStart_1438436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438481 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 4]
def baseStart_1438481 : Nat := 118140960795 + 1438481 * 2 ^ 59
def prefixEnd_1438481 : Nat := 4983230072969 + 3 ^ 40 * 1438481 * 2
def baseEnd_1438481 : Nat := 328280962382351853409801

theorem tailTrace_1438481 : CollatzResearch.WordTrace tailWord_1438481 prefixEnd_1438481 328280962382351853409801 := by
  unfold tailWord_1438481
  simp only [CollatzResearch.WordTrace]
  refine ⟨52465712301636484840883297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34977141534424323227255531 52465712301636484840883297)
  ·
    refine ⟨39349284226227363630662473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52465712301636484840883297 39349284226227363630662473)
    ·
      refine ⟨29511963169670522722996855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39349284226227363630662473 29511963169670522722996855)
      ·
        refine ⟨44267944754505784084495283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29511963169670522722996855 44267944754505784084495283)
        ·
          refine ⟨66401917131758676126742925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44267944754505784084495283 66401917131758676126742925)
          ·
            refine ⟨24900718924409503547528597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66401917131758676126742925 24900718924409503547528597)
            ·
              refine ⟨1167221199581695478790403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24900718924409503547528597 1167221199581695478790403)
              ·
                refine ⟨1750831799372543218185605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167221199581695478790403 1750831799372543218185605)
                ·
                  refine ⟨328280962382351853409801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1750831799372543218185605 328280962382351853409801)
                  ·
                    rfl

theorem cell21_1438481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_1438481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438481 prefixEnd_1438481 := by exact prefixLift 1438481
  have htrace : WordTrace (prefixWord ++ tailWord_1438481) baseStart_1438481 baseEnd_1438481 := by
    simpa [prefixWord, tailWord_1438481, baseEnd_1438481] using wordTrace_append hprefix tailTrace_1438481
  have hstable : (prefixWord ++ tailWord_1438481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438481).length < 2 ^ (prefixWord ++ tailWord_1438481).sum := by decide
  have hdescent : baseEnd_1438481 < baseStart_1438481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438518 : List Nat := [5, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_1438518 : Nat := 118140960795 + 1438518 * 2 ^ 59
def prefixEnd_1438518 : Nat := 4983230072969 + 3 ^ 40 * 1438518 * 2
def baseEnd_1438518 : Nat := 328289406286448011293059

theorem tailTrace_1438518 : CollatzResearch.WordTrace tailWord_1438518 prefixEnd_1438518 328289406286448011293059 := by
  unfold tailWord_1438518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3279191362656402509998763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34978041201668293439986805 3279191362656402509998763)
  ·
    refine ⟨4918787043984603764998145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3279191362656402509998763 4918787043984603764998145)
    ·
      refine ⟨3689090282988452823748609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4918787043984603764998145 3689090282988452823748609)
      ·
        refine ⟨2766817712241339617811457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3689090282988452823748609 2766817712241339617811457)
        ·
          refine ⟨2075113284181004713358593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2766817712241339617811457 2075113284181004713358593)
          ·
            refine ⟨1556334963135753535018945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2075113284181004713358593 1556334963135753535018945)
            ·
              refine ⟨1167251222351815151264209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1556334963135753535018945 1167251222351815151264209)
              ·
                refine ⟨875438416763861363448157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167251222351815151264209 875438416763861363448157)
                ·
                  refine ⟨328289406286448011293059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875438416763861363448157 328289406286448011293059)
                  ·
                    rfl

theorem cell21_1438518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_1438518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438518 prefixEnd_1438518 := by exact prefixLift 1438518
  have htrace : WordTrace (prefixWord ++ tailWord_1438518) baseStart_1438518 baseEnd_1438518 := by
    simpa [prefixWord, tailWord_1438518, baseEnd_1438518] using wordTrace_append hprefix tailTrace_1438518
  have hstable : (prefixWord ++ tailWord_1438518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438518).length < 2 ^ (prefixWord ++ tailWord_1438518).sum := by decide
  have hdescent : baseEnd_1438518 < baseStart_1438518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438529 : List Nat := [1, 2, 5, 3, 1, 2, 1, 6]
def baseStart_1438529 : Nat := 118140960795 + 1438529 * 2 ^ 59
def prefixEnd_1438529 : Nat := 4983230072969 + 3 ^ 40 * 1438529 * 2
def baseEnd_1438529 : Nat := 109430638878771478869901

theorem tailTrace_1438529 : CollatzResearch.WordTrace tailWord_1438529 prefixEnd_1438529 109430638878771478869901 := by
  unfold tailWord_1438529
  simp only [CollatzResearch.WordTrace]
  refine ⟨52467463005462589038630641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34978308670308392692420427 52467463005462589038630641)
  ·
    refine ⟨39350597254096941778972981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52467463005462589038630641 39350597254096941778972981)
    ·
      refine ⟨3689118492571588291778717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39350597254096941778972981 3689118492571588291778717)
      ·
        refine ⟨1383419434714345609417019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3689118492571588291778717 1383419434714345609417019)
        ·
          refine ⟨2075129152071518414125529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1383419434714345609417019 2075129152071518414125529)
          ·
            refine ⟨1556346864053638810594147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2075129152071518414125529 1556346864053638810594147)
            ·
              refine ⟨2334520296080458215891221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556346864053638810594147 2334520296080458215891221)
              ·
                refine ⟨109430638878771478869901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2334520296080458215891221 109430638878771478869901)
                ·
                  rfl

theorem cell21_1438529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 6].length) (baseStart_1438529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438529 prefixEnd_1438529 := by exact prefixLift 1438529
  have htrace : WordTrace (prefixWord ++ tailWord_1438529) baseStart_1438529 baseEnd_1438529 := by
    simpa [prefixWord, tailWord_1438529, baseEnd_1438529] using wordTrace_append hprefix tailTrace_1438529
  have hstable : (prefixWord ++ tailWord_1438529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438529).length < 2 ^ (prefixWord ++ tailWord_1438529).sum := by decide
  have hdescent : baseEnd_1438529 < baseStart_1438529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438585 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 5]
def baseStart_1438585 : Nat := 118140960795 + 1438585 * 2 ^ 59
def prefixEnd_1438585 : Nat := 4983230072969 + 3 ^ 40 * 1438585 * 2
def baseEnd_1438585 : Nat := 328304696599270783676255

theorem tailTrace_1438585 : CollatzResearch.WordTrace tailWord_1438585 prefixEnd_1438585 328304696599270783676255 := by
  unfold tailWord_1438585
  simp only [CollatzResearch.WordTrace]
  refine ⟨52469505493259710602669209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34979670328839807068446139 52469505493259710602669209)
  ·
    refine ⟨39352129119944782952001907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52469505493259710602669209 39352129119944782952001907)
    ·
      refine ⟨59028193679917174428002861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39352129119944782952001907 59028193679917174428002861)
      ·
        refine ⟨22135572629968940410501073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59028193679917174428002861 22135572629968940410501073)
        ·
          refine ⟨16601679472476705307875805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22135572629968940410501073 16601679472476705307875805)
          ·
            refine ⟨6225629802178764490453427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16601679472476705307875805 6225629802178764490453427)
            ·
              refine ⟨9338444703268146735680141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225629802178764490453427 9338444703268146735680141)
              ·
                refine ⟨3501916763725555025880053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9338444703268146735680141 3501916763725555025880053)
                ·
                  refine ⟨328304696599270783676255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3501916763725555025880053 328304696599270783676255)
                  ·
                    rfl

theorem cell21_1438585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_1438585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438585 prefixEnd_1438585 := by exact prefixLift 1438585
  have htrace : WordTrace (prefixWord ++ tailWord_1438585) baseStart_1438585 baseEnd_1438585 := by
    simpa [prefixWord, tailWord_1438585, baseEnd_1438585] using wordTrace_append hprefix tailTrace_1438585
  have hstable : (prefixWord ++ tailWord_1438585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438585).length < 2 ^ (prefixWord ++ tailWord_1438585).sum := by decide
  have hdescent : baseEnd_1438585 < baseStart_1438585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438602 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_1438602 : Nat := 118140960795 + 1438602 * 2 ^ 59
def prefixEnd_1438602 : Nat := 4983230072969 + 3 ^ 40 * 1438602 * 2
def baseEnd_1438602 : Nat := 328308576230882531892887

theorem tailTrace_1438602 : CollatzResearch.WordTrace tailWord_1438602 prefixEnd_1438602 328308576230882531892887 := by
  unfold tailWord_1438602
  simp only [CollatzResearch.WordTrace]
  refine ⟨13117531383549530626509515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34980083689465415004025373 13117531383549530626509515)
  ·
    refine ⟨19676297075324295939764273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13117531383549530626509515 19676297075324295939764273)
    ·
      refine ⟨14757222806493221954823205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19676297075324295939764273 14757222806493221954823205)
      ·
        refine ⟨2766979276217479116529351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14757222806493221954823205 2766979276217479116529351)
        ·
          refine ⟨4150468914326218674794027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2766979276217479116529351 4150468914326218674794027)
          ·
            refine ⟨6225703371489328012191041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150468914326218674794027 6225703371489328012191041)
            ·
              refine ⟨4669277528616996009143281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6225703371489328012191041 4669277528616996009143281)
              ·
                refine ⟨3501958146462747006857461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4669277528616996009143281 3501958146462747006857461)
                ·
                  refine ⟨328308576230882531892887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3501958146462747006857461 328308576230882531892887)
                  ·
                    rfl

theorem cell21_1438602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_1438602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438602 prefixEnd_1438602 := by exact prefixLift 1438602
  have htrace : WordTrace (prefixWord ++ tailWord_1438602) baseStart_1438602 baseEnd_1438602 := by
    simpa [prefixWord, tailWord_1438602, baseEnd_1438602] using wordTrace_append hprefix tailTrace_1438602
  have hstable : (prefixWord ++ tailWord_1438602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438602).length < 2 ^ (prefixWord ++ tailWord_1438602).sum := by decide
  have hdescent : baseEnd_1438602 < baseStart_1438602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438695 : List Nat := [1, 1, 5, 2, 2, 2, 1, 4, 3]
def baseStart_1438695 : Nat := 118140960795 + 1438695 * 2 ^ 59
def prefixEnd_1438695 : Nat := 4983230072969 + 3 ^ 40 * 1438695 * 2
def baseEnd_1438695 : Nat := 328329800097935036842697

theorem tailTrace_1438695 : CollatzResearch.WordTrace tailWord_1438695 prefixEnd_1438695 328329800097935036842697 := by
  unfold tailWord_1438695
  simp only [CollatzResearch.WordTrace]
  refine ⟨52473517522861199389173539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34982345015240799592782359 52473517522861199389173539)
  ·
    refine ⟨78710276284291799083760309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52473517522861199389173539 78710276284291799083760309)
    ·
      refine ⟨7379088401652356164102529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78710276284291799083760309 7379088401652356164102529)
      ·
        refine ⟨5534316301239267123076897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7379088401652356164102529 5534316301239267123076897)
        ·
          refine ⟨4150737225929450342307673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5534316301239267123076897 4150737225929450342307673)
          ·
            refine ⟨3113052919447087756730755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4150737225929450342307673 3113052919447087756730755)
            ·
              refine ⟨4669579379170631635096133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113052919447087756730755 4669579379170631635096133)
              ·
                refine ⟨875546133594493431580525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4669579379170631635096133 875546133594493431580525)
                ·
                  refine ⟨328329800097935036842697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875546133594493431580525 328329800097935036842697)
                  ·
                    rfl

theorem cell21_1438695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 3].length) (baseStart_1438695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438695 prefixEnd_1438695 := by exact prefixLift 1438695
  have htrace : WordTrace (prefixWord ++ tailWord_1438695) baseStart_1438695 baseEnd_1438695 := by
    simpa [prefixWord, tailWord_1438695, baseEnd_1438695] using wordTrace_append hprefix tailTrace_1438695
  have hstable : (prefixWord ++ tailWord_1438695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438695).length < 2 ^ (prefixWord ++ tailWord_1438695).sum := by decide
  have hdescent : baseEnd_1438695 < baseStart_1438695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438754 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1438754 : Nat := 118140960795 + 1438754 * 2 ^ 59
def prefixEnd_1438754 : Nat := 4983230072969 + 3 ^ 40 * 1438754 * 2
def baseEnd_1438754 : Nat := 328343264701764045359243

theorem tailTrace_1438754 : CollatzResearch.WordTrace tailWord_1438754 prefixEnd_1438754 328343264701764045359243 := by
  unfold tailWord_1438754
  simp only [CollatzResearch.WordTrace]
  refine ⟨13118917357411863116392829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34983779619764968310380877 13118917357411863116392829)
  ·
    refine ⟨4919594009029448668647311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13118917357411863116392829 4919594009029448668647311)
    ·
      refine ⟨7379391013544173002970967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919594009029448668647311 7379391013544173002970967)
      ·
        refine ⟨11069086520316259504456451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7379391013544173002970967 11069086520316259504456451)
        ·
          refine ⟨16603629780474389256684677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11069086520316259504456451 16603629780474389256684677)
          ·
            refine ⟨3113180583838947985628377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16603629780474389256684677 3113180583838947985628377)
            ·
              refine ⟨2334885437879210989221283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3113180583838947985628377 2334885437879210989221283)
              ·
                refine ⟨3502328156818816483831925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2334885437879210989221283 3502328156818816483831925)
                ·
                  refine ⟨328343264701764045359243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3502328156818816483831925 328343264701764045359243)
                  ·
                    rfl

theorem cell21_1438754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1438754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438754 prefixEnd_1438754 := by exact prefixLift 1438754
  have htrace : WordTrace (prefixWord ++ tailWord_1438754) baseStart_1438754 baseEnd_1438754 := by
    simpa [prefixWord, tailWord_1438754, baseEnd_1438754] using wordTrace_append hprefix tailTrace_1438754
  have hstable : (prefixWord ++ tailWord_1438754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438754).length < 2 ^ (prefixWord ++ tailWord_1438754).sum := by decide
  have hdescent : baseEnd_1438754 < baseStart_1438754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438903 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 6]
def baseStart_1438903 : Nat := 118140960795 + 1438903 * 2 ^ 59
def prefixEnd_1438903 : Nat := 4983230072969 + 3 ^ 40 * 1438903 * 2
def baseEnd_1438903 : Nat := 328377268531772897375605

theorem tailTrace_1438903 : CollatzResearch.WordTrace tailWord_1438903 prefixEnd_1438903 328377268531772897375605 := by
  unfold tailWord_1438903
  simp only [CollatzResearch.WordTrace]
  refine ⟨52481103906107650912745363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34987402604071767275163575 52481103906107650912745363)
  ·
    refine ⟨78721655859161476369118045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52481103906107650912745363 78721655859161476369118045)
    ·
      refine ⟨29520620947185553638419267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78721655859161476369118045 29520620947185553638419267)
      ·
        refine ⟨44280931420778330457628901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29520620947185553638419267 44280931420778330457628901)
        ·
          refine ⟨8302674641395936960805419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44280931420778330457628901 8302674641395936960805419)
          ·
            refine ⟨12454011962093905441208129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8302674641395936960805419 12454011962093905441208129)
            ·
              refine ⟨9340508971570429080906097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12454011962093905441208129 9340508971570429080906097)
              ·
                refine ⟨7005381728677821810679573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9340508971570429080906097 7005381728677821810679573)
                ·
                  refine ⟨328377268531772897375605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7005381728677821810679573 328377268531772897375605)
                  ·
                    rfl

theorem cell21_1438903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_1438903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438903 prefixEnd_1438903 := by exact prefixLift 1438903
  have htrace : WordTrace (prefixWord ++ tailWord_1438903) baseStart_1438903 baseEnd_1438903 := by
    simpa [prefixWord, tailWord_1438903, baseEnd_1438903] using wordTrace_append hprefix tailTrace_1438903
  have hstable : (prefixWord ++ tailWord_1438903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438903).length < 2 ^ (prefixWord ++ tailWord_1438903).sum := by decide
  have hdescent : baseEnd_1438903 < baseStart_1438903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438920 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 4]
def baseStart_1438920 : Nat := 118140960795 + 1438920 * 2 ^ 59
def prefixEnd_1438920 : Nat := 4983230072969 + 3 ^ 40 * 1438920 * 2
def baseEnd_1438920 : Nat := 328381148163384645592237

theorem tailTrace_1438920 : CollatzResearch.WordTrace tailWord_1438920 prefixEnd_1438920 328381148163384645592237 := by
  unfold tailWord_1438920
  simp only [CollatzResearch.WordTrace]
  refine ⟨26240861973523031408057107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34987815964697375210742809 26240861973523031408057107)
  ·
    refine ⟨39361292960284547112085661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26240861973523031408057107 39361292960284547112085661)
    ·
      refine ⟨14760484860106705167032123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39361292960284547112085661 14760484860106705167032123)
      ·
        refine ⟨22140727290160057750548185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14760484860106705167032123 22140727290160057750548185)
        ·
          refine ⟨16605545467620043312911139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22140727290160057750548185 16605545467620043312911139)
          ·
            refine ⟨24908318201430064969366709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16605545467620043312911139 24908318201430064969366709)
            ·
              refine ⟨2335154831384068590878129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24908318201430064969366709 2335154831384068590878129)
              ·
                refine ⟨1751366123538051443158597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2335154831384068590878129 1751366123538051443158597)
                ·
                  refine ⟨328381148163384645592237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1751366123538051443158597 328381148163384645592237)
                  ·
                    rfl

theorem cell21_1438920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_1438920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438920 prefixEnd_1438920 := by exact prefixLift 1438920
  have htrace : WordTrace (prefixWord ++ tailWord_1438920) baseStart_1438920 baseEnd_1438920 := by
    simpa [prefixWord, tailWord_1438920, baseEnd_1438920] using wordTrace_append hprefix tailTrace_1438920
  have hstable : (prefixWord ++ tailWord_1438920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438920).length < 2 ^ (prefixWord ++ tailWord_1438920).sum := by decide
  have hdescent : baseEnd_1438920 < baseStart_1438920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438951 : List Nat := [1, 1, 5, 3, 2, 1, 1, 7]
def baseStart_1438951 : Nat := 118140960795 + 1438951 * 2 ^ 59
def prefixEnd_1438951 : Nat := 4983230072969 + 3 ^ 40 * 1438951 * 2
def baseEnd_1438951 : Nat := 109462740928578493525169

theorem tailTrace_1438951 : CollatzResearch.WordTrace tailWord_1438951 prefixEnd_1438951 109462740928578493525169 := by
  unfold tailWord_1438951
  simp only [CollatzResearch.WordTrace]
  refine ⟨52482854609933755110492707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34988569739955836740328471 52482854609933755110492707)
  ·
    refine ⟨78724281914900632665739061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52482854609933755110492707 78724281914900632665739061)
    ·
      refine ⟨7380401429521934312413037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78724281914900632665739061 7380401429521934312413037)
      ·
        refine ⟨2767650536070725367154889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7380401429521934312413037 2767650536070725367154889)
        ·
          refine ⟨2075737902053044025366167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2767650536070725367154889 2075737902053044025366167)
          ·
            refine ⟨3113606853079566038049251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075737902053044025366167 3113606853079566038049251)
            ·
              refine ⟨4670410279619349057073877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113606853079566038049251 4670410279619349057073877)
              ·
                refine ⟨109462740928578493525169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4670410279619349057073877 109462740928578493525169)
                ·
                  rfl

theorem cell21_1438951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 7].length) (baseStart_1438951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438951 prefixEnd_1438951 := by exact prefixLift 1438951
  have htrace : WordTrace (prefixWord ++ tailWord_1438951) baseStart_1438951 baseEnd_1438951 := by
    simpa [prefixWord, tailWord_1438951, baseEnd_1438951] using wordTrace_append hprefix tailTrace_1438951
  have hstable : (prefixWord ++ tailWord_1438951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438951).length < 2 ^ (prefixWord ++ tailWord_1438951).sum := by decide
  have hdescent : baseEnd_1438951 < baseStart_1438951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438979 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 6]
def baseStart_1438979 : Nat := 118140960795 + 1438979 * 2 ^ 59
def prefixEnd_1438979 : Nat := 4983230072969 + 3 ^ 40 * 1438979 * 2
def baseEnd_1438979 : Nat := 328394612767213654108783

theorem tailTrace_1438979 : CollatzResearch.WordTrace tailWord_1438979 prefixEnd_1438979 328394612767213654108783 := by
  unfold tailWord_1438979
  simp only [CollatzResearch.WordTrace]
  refine ⟨52483875853832315892511991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34989250569221543928341327 52483875853832315892511991)
  ·
    refine ⟨78725813780748473838767987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52483875853832315892511991 78725813780748473838767987)
    ·
      refine ⟨118088720671122710758151981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78725813780748473838767987 118088720671122710758151981)
      ·
        refine ⟨44283270251671016534306993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118088720671122710758151981 44283270251671016534306993)
        ·
          refine ⟨33212452688753262400730245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44283270251671016534306993 33212452688753262400730245)
          ·
            refine ⟨6227334879141236700136921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33212452688753262400730245 6227334879141236700136921)
            ·
              refine ⟨4670501159355927525102691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6227334879141236700136921 4670501159355927525102691)
              ·
                refine ⟨7005751739033891287654037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670501159355927525102691 7005751739033891287654037)
                ·
                  refine ⟨328394612767213654108783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7005751739033891287654037 328394612767213654108783)
                  ·
                    rfl

theorem cell21_1438979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_1438979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1438979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1438979 prefixEnd_1438979 := by exact prefixLift 1438979
  have htrace : WordTrace (prefixWord ++ tailWord_1438979) baseStart_1438979 baseEnd_1438979 := by
    simpa [prefixWord, tailWord_1438979, baseEnd_1438979] using wordTrace_append hprefix tailTrace_1438979
  have hstable : (prefixWord ++ tailWord_1438979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438979).length < 2 ^ (prefixWord ++ tailWord_1438979).sum := by decide
  have hdescent : baseEnd_1438979 < baseStart_1438979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439033 : List Nat := [1, 2, 1, 6, 3, 1, 2, 2, 3]
def baseStart_1439033 : Nat := 118140960795 + 1439033 * 2 ^ 59
def prefixEnd_1439033 : Nat := 4983230072969 + 3 ^ 40 * 1439033 * 2
def baseEnd_1439033 : Nat := 328406936302921560208673

theorem tailTrace_1439033 : CollatzResearch.WordTrace tailWord_1439033 prefixEnd_1439033 328406936302921560208673 := by
  unfold tailWord_1439033
  simp only [CollatzResearch.WordTrace]
  refine ⟨52485845395636683114977753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34990563597091122076651835 52485845395636683114977753)
  ·
    refine ⟨39364384046727512336233315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52485845395636683114977753 39364384046727512336233315)
    ·
      refine ⟨59046576070091268504349973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39364384046727512336233315 59046576070091268504349973)
      ·
        refine ⟨2767808253285528211141405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59046576070091268504349973 2767808253285528211141405)
        ·
          refine ⟨1037928094982073079178027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2767808253285528211141405 1037928094982073079178027)
          ·
            refine ⟨1556892142473109618767041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037928094982073079178027 1556892142473109618767041)
            ·
              refine ⟨1167669106854832214075281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1556892142473109618767041 1167669106854832214075281)
              ·
                refine ⟨875751830141124160556461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167669106854832214075281 875751830141124160556461)
                ·
                  refine ⟨328406936302921560208673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875751830141124160556461 328406936302921560208673)
                  ·
                    rfl

theorem cell21_1439033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 3].length) (baseStart_1439033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439033 prefixEnd_1439033 := by exact prefixLift 1439033
  have htrace : WordTrace (prefixWord ++ tailWord_1439033) baseStart_1439033 baseEnd_1439033 := by
    simpa [prefixWord, tailWord_1439033, baseEnd_1439033] using wordTrace_append hprefix tailTrace_1439033
  have hstable : (prefixWord ++ tailWord_1439033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439033).length < 2 ^ (prefixWord ++ tailWord_1439033).sum := by decide
  have hdescent : baseEnd_1439033 < baseStart_1439033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439044 : List Nat := [2, 3, 4, 1, 1, 3, 1, 6]
def baseStart_1439044 : Nat := 118140960795 + 1439044 * 2 ^ 59
def prefixEnd_1439044 : Nat := 4983230072969 + 3 ^ 40 * 1439044 * 2
def baseEnd_1439044 : Nat := 109469815550929328508439

theorem tailTrace_1439044 : CollatzResearch.WordTrace tailWord_1439044 prefixEnd_1439044 109469815550929328508439 := by
  unfold tailWord_1439044
  simp only [CollatzResearch.WordTrace]
  refine ⟨26243123299298415996814093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34990831065731221329085457 26243123299298415996814093)
  ·
    refine ⟨9841171237236905998805285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26243123299298415996814093 9841171237236905998805285)
    ·
      refine ⟨1845219606981919874775991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9841171237236905998805285 1845219606981919874775991)
      ·
        refine ⟨2767829410472879812163987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845219606981919874775991 2767829410472879812163987)
        ·
          refine ⟨4151744115709319718245981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767829410472879812163987 4151744115709319718245981)
          ·
            refine ⟨1556904043390994894342243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4151744115709319718245981 1556904043390994894342243)
            ·
              refine ⟨2335356065086492341513365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556904043390994894342243 2335356065086492341513365)
              ·
                refine ⟨109469815550929328508439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2335356065086492341513365 109469815550929328508439)
                ·
                  rfl

theorem cell21_1439044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_1439044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439044 prefixEnd_1439044 := by exact prefixLift 1439044
  have htrace : WordTrace (prefixWord ++ tailWord_1439044) baseStart_1439044 baseEnd_1439044 := by
    simpa [prefixWord, tailWord_1439044, baseEnd_1439044] using wordTrace_append hprefix tailTrace_1439044
  have hstable : (prefixWord ++ tailWord_1439044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439044).length < 2 ^ (prefixWord ++ tailWord_1439044).sum := by decide
  have hdescent : baseEnd_1439044 < baseStart_1439044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439176 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_1439176 : Nat := 118140960795 + 1439176 * 2 ^ 59
def prefixEnd_1439176 : Nat := 4983230072969 + 3 ^ 40 * 1439176 * 2
def baseEnd_1439176 : Nat := 328439570851185089325047

theorem tailTrace_1439176 : CollatzResearch.WordTrace tailWord_1439176 prefixEnd_1439176 328439570851185089325047 := by
  unfold tailWord_1439176
  simp only [CollatzResearch.WordTrace]
  refine ⟨26245530517059309268716691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34994040689412412358288921 26245530517059309268716691)
  ·
    refine ⟨39368295775588963903075037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26245530517059309268716691 39368295775588963903075037)
    ·
      refine ⟨14763110915845861463653139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39368295775588963903075037 14763110915845861463653139)
      ·
        refine ⟨22144666373768792195479709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14763110915845861463653139 22144666373768792195479709)
        ·
          refine ⟨8304249890163297073304891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22144666373768792195479709 8304249890163297073304891)
          ·
            refine ⟨12456374835244945609957337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8304249890163297073304891 12456374835244945609957337)
            ·
              refine ⟨9342281126433709207468003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12456374835244945609957337 9342281126433709207468003)
              ·
                refine ⟨14013421689650563811202005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9342281126433709207468003 14013421689650563811202005)
                ·
                  refine ⟨328439570851185089325047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14013421689650563811202005 328439570851185089325047)
                  ·
                    rfl

theorem cell21_1439176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_1439176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439176 prefixEnd_1439176 := by exact prefixLift 1439176
  have htrace : WordTrace (prefixWord ++ tailWord_1439176) baseStart_1439176 baseEnd_1439176 := by
    simpa [prefixWord, tailWord_1439176, baseEnd_1439176] using wordTrace_append hprefix tailTrace_1439176
  have hstable : (prefixWord ++ tailWord_1439176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439176).length < 2 ^ (prefixWord ++ tailWord_1439176).sum := by decide
  have hdescent : baseEnd_1439176 < baseStart_1439176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439303 : List Nat := [1, 1, 4, 1, 5, 2, 1, 3, 3]
def baseStart_1439303 : Nat := 118140960795 + 1439303 * 2 ^ 59
def prefixEnd_1439303 : Nat := 4983230072969 + 3 ^ 40 * 1439303 * 2
def baseEnd_1439303 : Nat := 328468553981461090708121

theorem tailTrace_1439303 : CollatzResearch.WordTrace tailWord_1439303 prefixEnd_1439303 328468553981461090708121 := by
  unfold tailWord_1439303
  simp only [CollatzResearch.WordTrace]
  refine ⟨52495693104658519227306563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34997128736439012818204375 52495693104658519227306563)
  ·
    refine ⟨78743539656987778840959845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52495693104658519227306563 78743539656987778840959845)
    ·
      refine ⟨14764413685685208532679971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78743539656987778840959845 14764413685685208532679971)
      ·
        refine ⟨22146620528527812799019957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14764413685685208532679971 22146620528527812799019957)
        ·
          refine ⟨2076245674549482449908121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22146620528527812799019957 2076245674549482449908121)
          ·
            refine ⟨1557184255912111837431091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2076245674549482449908121 1557184255912111837431091)
            ·
              refine ⟨2335776383868167756146637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557184255912111837431091 2335776383868167756146637)
              ·
                refine ⟨875916143950562908554989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2335776383868167756146637 875916143950562908554989)
                ·
                  refine ⟨328468553981461090708121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875916143950562908554989 328468553981461090708121)
                  ·
                    rfl

theorem cell21_1439303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 3].length) (baseStart_1439303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439303 prefixEnd_1439303 := by exact prefixLift 1439303
  have htrace : WordTrace (prefixWord ++ tailWord_1439303) baseStart_1439303 baseEnd_1439303 := by
    simpa [prefixWord, tailWord_1439303, baseEnd_1439303] using wordTrace_append hprefix tailTrace_1439303
  have hstable : (prefixWord ++ tailWord_1439303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439303).length < 2 ^ (prefixWord ++ tailWord_1439303).sum := by decide
  have hdescent : baseEnd_1439303 < baseStart_1439303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439314 : List Nat := [3, 2, 2, 1, 2, 4, 7]
def baseStart_1439314 : Nat := 118140960795 + 1439314 * 2 ^ 59
def prefixEnd_1439314 : Nat := 4983230072969 + 3 ^ 40 * 1439314 * 2
def baseEnd_1439314 : Nat := 36496784925703057336085

theorem tailTrace_1439314 : CollatzResearch.WordTrace tailWord_1439314 prefixEnd_1439314 36496784925703057336085 := by
  unfold tailWord_1439314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13124023576904667026489249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34997396205079112070637997 13124023576904667026489249)
  ·
    refine ⟨9843017682678500269866937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13124023576904667026489249 9843017682678500269866937)
    ·
      refine ⟨7382263262008875202400203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9843017682678500269866937 7382263262008875202400203)
      ·
        refine ⟨11073394893013312803600305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7382263262008875202400203 11073394893013312803600305)
        ·
          refine ⟨8305046169759984602700229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11073394893013312803600305 8305046169759984602700229)
          ·
            refine ⟨1557196156829997113006293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8305046169759984602700229 1557196156829997113006293)
            ·
              refine ⟨36496784925703057336085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1557196156829997113006293 36496784925703057336085)
              ·
                rfl

theorem cell21_1439314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 7].length) (baseStart_1439314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439314 prefixEnd_1439314 := by exact prefixLift 1439314
  have htrace : WordTrace (prefixWord ++ tailWord_1439314) baseStart_1439314 baseEnd_1439314 := by
    simpa [prefixWord, tailWord_1439314, baseEnd_1439314] using wordTrace_append hprefix tailTrace_1439314
  have hstable : (prefixWord ++ tailWord_1439314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439314).length < 2 ^ (prefixWord ++ tailWord_1439314).sum := by decide
  have hdescent : baseEnd_1439314 < baseStart_1439314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439466 : List Nat := [3, 1, 3, 1, 1, 1, 6, 5]
def baseStart_1439466 : Nat := 118140960795 + 1439466 * 2 ^ 59
def prefixEnd_1439466 : Nat := 4983230072969 + 3 ^ 40 * 1439466 * 2
def baseEnd_1439466 : Nat := 109501917600736343163707

theorem tailTrace_1439466 : CollatzResearch.WordTrace tailWord_1439466 prefixEnd_1439466 109501917600736343163707 := by
  unfold tailWord_1439466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13125409550766999516372563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35001092135378665376993501 13125409550766999516372563)
  ·
    refine ⟨19688114326150499274558845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13125409550766999516372563 19688114326150499274558845)
    ·
      refine ⟨7383042872306437227959567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19688114326150499274558845 7383042872306437227959567)
      ·
        refine ⟨11074564308459655841939351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7383042872306437227959567 11074564308459655841939351)
        ·
          refine ⟨16611846462689483762909027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11074564308459655841939351 16611846462689483762909027)
          ·
            refine ⟨24917769694034225644363541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16611846462689483762909027 24917769694034225644363541)
            ·
              refine ⟨1168020454407854327079541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24917769694034225644363541 1168020454407854327079541)
              ·
                refine ⟨109501917600736343163707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1168020454407854327079541 109501917600736343163707)
                ·
                  rfl

theorem cell21_1439466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_1439466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439466 prefixEnd_1439466 := by exact prefixLift 1439466
  have htrace : WordTrace (prefixWord ++ tailWord_1439466) baseStart_1439466 baseEnd_1439466 := by
    simpa [prefixWord, tailWord_1439466, baseEnd_1439466] using wordTrace_append hprefix tailTrace_1439466
  have hstable : (prefixWord ++ tailWord_1439466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439466).length < 2 ^ (prefixWord ++ tailWord_1439466).sum := by decide
  have hdescent : baseEnd_1439466 < baseStart_1439466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439525 : List Nat := [1, 3, 1, 2, 3, 2, 2, 7]
def baseStart_1439525 : Nat := 118140960795 + 1439525 * 2 ^ 59
def prefixEnd_1439525 : Nat := 4983230072969 + 3 ^ 40 * 1439525 * 2
def baseEnd_1439525 : Nat := 109506405802012679335889

theorem tailTrace_1439525 : CollatzResearch.WordTrace tailWord_1439525 prefixEnd_1439525 109506405802012679335889 := by
  unfold tailWord_1439525
  simp only [CollatzResearch.WordTrace]
  refine ⟨52503790109854251141888029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35002526739902834094592019 52503790109854251141888029)
  ·
    refine ⟨19688921291195344178208011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52503790109854251141888029 19688921291195344178208011)
    ·
      refine ⟨29533381936793016267312017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19688921291195344178208011 29533381936793016267312017)
      ·
        refine ⟨22150036452594762200484013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29533381936793016267312017 22150036452594762200484013)
        ·
          refine ⟨8306263669723035825181505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22150036452594762200484013 8306263669723035825181505)
          ·
            refine ⟨6229697752292276868886129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8306263669723035825181505 6229697752292276868886129)
            ·
              refine ⟨4672273314219207651664597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6229697752292276868886129 4672273314219207651664597)
              ·
                refine ⟨109506405802012679335889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4672273314219207651664597 109506405802012679335889)
                ·
                  rfl

theorem cell21_1439525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 7].length) (baseStart_1439525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439525 prefixEnd_1439525 := by exact prefixLift 1439525
  have htrace : WordTrace (prefixWord ++ tailWord_1439525) baseStart_1439525 baseEnd_1439525 := by
    simpa [prefixWord, tailWord_1439525, baseEnd_1439525] using wordTrace_append hprefix tailTrace_1439525
  have hstable : (prefixWord ++ tailWord_1439525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439525).length < 2 ^ (prefixWord ++ tailWord_1439525).sum := by decide
  have hdescent : baseEnd_1439525 < baseStart_1439525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439542 : List Nat := [5, 1, 2, 2, 1, 10]
def baseStart_1439542 : Nat := 118140960795 + 1439542 * 2 ^ 59
def prefixEnd_1439542 : Nat := 4983230072969 + 3 ^ 40 * 1439542 * 2
def baseEnd_1439542 : Nat := 12167522112505547637937

theorem tailTrace_1439542 : CollatzResearch.WordTrace tailWord_1439542 prefixEnd_1439542 12167522112505547637937 := by
  unfold tailWord_1439542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281525634424541440328555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35002940100528442030171253 3281525634424541440328555)
  ·
    refine ⟨4922288451636812160492833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3281525634424541440328555 4922288451636812160492833)
    ·
      refine ⟨3691716338727609120369625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4922288451636812160492833 3691716338727609120369625)
      ·
        refine ⟨2768787254045706840277219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3691716338727609120369625 2768787254045706840277219)
        ·
          refine ⟨4153180881068560260415829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2768787254045706840277219 4153180881068560260415829)
          ·
            refine ⟨12167522112505547637937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4153180881068560260415829 12167522112505547637937)
            ·
              rfl

theorem cell21_1439542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 10].length) (baseStart_1439542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439542 prefixEnd_1439542 := by exact prefixLift 1439542
  have htrace : WordTrace (prefixWord ++ tailWord_1439542) baseStart_1439542 baseEnd_1439542 := by
    simpa [prefixWord, tailWord_1439542, baseEnd_1439542] using wordTrace_append hprefix tailTrace_1439542
  have hstable : (prefixWord ++ tailWord_1439542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439542).length < 2 ^ (prefixWord ++ tailWord_1439542).sum := by decide
  have hdescent : baseEnd_1439542 < baseStart_1439542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439545 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 4]
def baseStart_1439545 : Nat := 118140960795 + 1439545 * 2 ^ 59
def prefixEnd_1439545 : Nat := 4983230072969 + 3 ^ 40 * 1439545 * 2
def baseEnd_1439545 : Nat := 328523781678522447674293

theorem tailTrace_1439545 : CollatzResearch.WordTrace tailWord_1439545 prefixEnd_1439545 328523781678522447674293 := by
  unfold tailWord_1439545
  simp only [CollatzResearch.WordTrace]
  refine ⟨52504519569781794557616089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35003013046521196371744059 52504519569781794557616089)
  ·
    refine ⟨39378389677336345918212067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52504519569781794557616089 39378389677336345918212067)
    ·
      refine ⟨59067584516004518877318101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39378389677336345918212067 59067584516004518877318101)
      ·
        refine ⟨1384396512093855911187143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 59067584516004518877318101 1384396512093855911187143)
        ·
          refine ⟨2076594768140783866780715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384396512093855911187143 2076594768140783866780715)
          ·
            refine ⟨3114892152211175800171073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2076594768140783866780715 3114892152211175800171073)
            ·
              refine ⟨2336169114158381850128305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3114892152211175800171073 2336169114158381850128305)
              ·
                refine ⟨1752126835618786387596229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2336169114158381850128305 1752126835618786387596229)
                ·
                  refine ⟨328523781678522447674293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1752126835618786387596229 328523781678522447674293)
                  ·
                    rfl

theorem cell21_1439545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_1439545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439545 prefixEnd_1439545 := by exact prefixLift 1439545
  have htrace : WordTrace (prefixWord ++ tailWord_1439545) baseStart_1439545 baseEnd_1439545 := by
    simpa [prefixWord, tailWord_1439545, baseEnd_1439545] using wordTrace_append hprefix tailTrace_1439545
  have hstable : (prefixWord ++ tailWord_1439545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439545).length < 2 ^ (prefixWord ++ tailWord_1439545).sum := by decide
  have hdescent : baseEnd_1439545 < baseStart_1439545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439677 : List Nat := [1, 4, 1, 2, 3, 1, 1, 8]
def baseStart_1439677 : Nat := 118140960795 + 1439677 * 2 ^ 59
def prefixEnd_1439677 : Nat := 4983230072969 + 3 ^ 40 * 1439677 * 2
def baseEnd_1439677 : Nat := 109517968625639850491341

theorem tailTrace_1439677 : CollatzResearch.WordTrace tailWord_1439677 prefixEnd_1439677 109517968625639850491341 := by
  unfold tailWord_1439677
  simp only [CollatzResearch.WordTrace]
  refine ⟨52509334005303581101421285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35006222670202387400947523 52509334005303581101421285)
  ·
    refine ⟨9845500125994421456516491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52509334005303581101421285 9845500125994421456516491)
    ·
      refine ⟨14768250188991632184774737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9845500125994421456516491 14768250188991632184774737)
      ·
        refine ⟨11076187641743724138581053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14768250188991632184774737 11076187641743724138581053)
        ·
          refine ⟨4153570365653896551967895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11076187641743724138581053 4153570365653896551967895)
          ·
            refine ⟨6230355548480844827951843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4153570365653896551967895 6230355548480844827951843)
            ·
              refine ⟨9345533322721267241927765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6230355548480844827951843 9345533322721267241927765)
              ·
                refine ⟨109517968625639850491341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9345533322721267241927765 109517968625639850491341)
                ·
                  rfl

theorem cell21_1439677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 8].length) (baseStart_1439677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439677 prefixEnd_1439677 := by exact prefixLift 1439677
  have htrace : WordTrace (prefixWord ++ tailWord_1439677) baseStart_1439677 baseEnd_1439677 := by
    simpa [prefixWord, tailWord_1439677, baseEnd_1439677] using wordTrace_append hprefix tailTrace_1439677
  have hstable : (prefixWord ++ tailWord_1439677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439677).length < 2 ^ (prefixWord ++ tailWord_1439677).sum := by decide
  have hdescent : baseEnd_1439677 < baseStart_1439677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439691 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 7]
def baseStart_1439691 : Nat := 118140960795 + 1439691 * 2 ^ 59
def prefixEnd_1439691 : Nat := 4983230072969 + 3 ^ 40 * 1439691 * 2
def baseEnd_1439691 : Nat := 328557100867658638240661

theorem tailTrace_1439691 : CollatzResearch.WordTrace tailWord_1439691 prefixEnd_1439691 328557100867658638240661 := by
  unfold tailWord_1439691
  simp only [CollatzResearch.WordTrace]
  refine ⟨52509844627252861492430927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35006563084835240994953951 52509844627252861492430927)
  ·
    refine ⟨78764766940879292238646391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52509844627252861492430927 78764766940879292238646391)
    ·
      refine ⟨118147150411318938357969587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78764766940879292238646391 118147150411318938357969587)
      ·
        refine ⟨177220725616978407536954381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118147150411318938357969587 177220725616978407536954381)
        ·
          refine ⟨66457772106366902826357893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177220725616978407536954381 66457772106366902826357893)
          ·
            refine ⟨12460832269943794279942105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66457772106366902826357893 12460832269943794279942105)
            ·
              refine ⟨9345624202457845709956579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12460832269943794279942105 9345624202457845709956579)
              ·
                refine ⟨14018436303686768564934869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9345624202457845709956579 14018436303686768564934869)
                ·
                  refine ⟨328557100867658638240661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14018436303686768564934869 328557100867658638240661)
                  ·
                    rfl

theorem cell21_1439691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_1439691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439691 prefixEnd_1439691 := by exact prefixLift 1439691
  have htrace : WordTrace (prefixWord ++ tailWord_1439691) baseStart_1439691 baseEnd_1439691 := by
    simpa [prefixWord, tailWord_1439691, baseEnd_1439691] using wordTrace_append hprefix tailTrace_1439691
  have hstable : (prefixWord ++ tailWord_1439691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439691).length < 2 ^ (prefixWord ++ tailWord_1439691).sum := by decide
  have hdescent : baseEnd_1439691 < baseStart_1439691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439829 : List Nat := [1, 3, 2, 2, 1, 5, 7]
def baseStart_1439829 : Nat := 118140960795 + 1439829 * 2 ^ 59
def prefixEnd_1439829 : Nat := 4983230072969 + 3 ^ 40 * 1439829 * 2
def baseEnd_1439829 : Nat := 36509843816422340548931

theorem tailTrace_1439829 : CollatzResearch.WordTrace tailWord_1439829 prefixEnd_1439829 36509843816422340548931 := by
  unfold tailWord_1439829
  simp only [CollatzResearch.WordTrace]
  refine ⟨52514877900752911060954541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35009918600501940707303027 52514877900752911060954541)
  ·
    refine ⟨19693079212782341647857953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52514877900752911060954541 19693079212782341647857953)
    ·
      refine ⟨14769809409586756235893465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19693079212782341647857953 14769809409586756235893465)
      ·
        refine ⟨11077357057190067176920099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14769809409586756235893465 11077357057190067176920099)
        ·
          refine ⟨16616035585785100765380149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11077357057190067176920099 16616035585785100765380149)
          ·
            refine ⟨1557753336167353196754389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16616035585785100765380149 1557753336167353196754389)
            ·
              refine ⟨36509843816422340548931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1557753336167353196754389 36509843816422340548931)
              ·
                rfl

theorem cell21_1439829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 7].length) (baseStart_1439829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439829 prefixEnd_1439829 := by exact prefixLift 1439829
  have htrace : WordTrace (prefixWord ++ tailWord_1439829) baseStart_1439829 baseEnd_1439829 := by
    simpa [prefixWord, tailWord_1439829, baseEnd_1439829] using wordTrace_append hprefix tailTrace_1439829
  have hstable : (prefixWord ++ tailWord_1439829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439829).length < 2 ^ (prefixWord ++ tailWord_1439829).sum := by decide
  have hdescent : baseEnd_1439829 < baseStart_1439829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439905 : List Nat := [1, 2, 3, 3, 1, 2, 3, 6]
def baseStart_1439905 : Nat := 118140960795 + 1439905 * 2 ^ 59
def prefixEnd_1439905 : Nat := 4983230072969 + 3 ^ 40 * 1439905 * 2
def baseEnd_1439905 : Nat := 109535312861080607224519

theorem tailTrace_1439905 : CollatzResearch.WordTrace tailWord_1439905 prefixEnd_1439905 109535312861080607224519 := by
  unfold tailWord_1439905
  simp only [CollatzResearch.WordTrace]
  refine ⟨52517649848477576040721169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35011766565651717360480779 52517649848477576040721169)
  ·
    refine ⟨39388237386358182030540877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52517649848477576040721169 39388237386358182030540877)
    ·
      refine ⟨14770589019884318261452829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39388237386358182030540877 14770589019884318261452829)
      ·
        refine ⟨5538970882456619348044811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14770589019884318261452829 5538970882456619348044811)
        ·
          refine ⟨8308456323684929022067217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5538970882456619348044811 8308456323684929022067217)
          ·
            refine ⟨6231342242763696766550413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8308456323684929022067217 6231342242763696766550413)
            ·
              refine ⟨2336753341036386287456405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6231342242763696766550413 2336753341036386287456405)
              ·
                refine ⟨109535312861080607224519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2336753341036386287456405 109535312861080607224519)
                ·
                  rfl

theorem cell21_1439905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 6].length) (baseStart_1439905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1439905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1439905 prefixEnd_1439905 := by exact prefixLift 1439905
  have htrace : WordTrace (prefixWord ++ tailWord_1439905) baseStart_1439905 baseEnd_1439905 := by
    simpa [prefixWord, tailWord_1439905, baseEnd_1439905] using wordTrace_append hprefix tailTrace_1439905
  have hstable : (prefixWord ++ tailWord_1439905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439905).length < 2 ^ (prefixWord ++ tailWord_1439905).sum := by decide
  have hdescent : baseEnd_1439905 < baseStart_1439905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440071 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 5]
def baseStart_1440071 : Nat := 118140960795 + 1440071 * 2 ^ 59
def prefixEnd_1440071 : Nat := 4983230072969 + 3 ^ 40 * 1440071 * 2
def baseEnd_1440071 : Nat := 328643822044862421906551

theorem tailTrace_1440071 : CollatzResearch.WordTrace tailWord_1440071 prefixEnd_1440071 328643822044862421906551 := by
  unfold tailWord_1440071
  simp only [CollatzResearch.WordTrace]
  refine ⟨52523704365876186391264067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35015802910584124260842711 52523704365876186391264067)
  ·
    refine ⟨78785556548814279586896101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52523704365876186391264067 78785556548814279586896101)
    ·
      refine ⟨14772291852902677422543019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78785556548814279586896101 14772291852902677422543019)
      ·
        refine ⟨22158437779354016133814529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14772291852902677422543019 22158437779354016133814529)
        ·
          refine ⟨16618828334515512100360897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22158437779354016133814529 16618828334515512100360897)
          ·
            refine ⟨12464121250886634075270673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16618828334515512100360897 12464121250886634075270673)
            ·
              refine ⟨9348090938164975556453005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12464121250886634075270673 9348090938164975556453005)
              ·
                refine ⟨3505534101811865833669877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9348090938164975556453005 3505534101811865833669877)
                ·
                  refine ⟨328643822044862421906551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3505534101811865833669877 328643822044862421906551)
                  ·
                    rfl

theorem cell21_1440071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_1440071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440071 prefixEnd_1440071 := by exact prefixLift 1440071
  have htrace : WordTrace (prefixWord ++ tailWord_1440071) baseStart_1440071 baseEnd_1440071 := by
    simpa [prefixWord, tailWord_1440071, baseEnd_1440071] using wordTrace_append hprefix tailTrace_1440071
  have hstable : (prefixWord ++ tailWord_1440071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440071).length < 2 ^ (prefixWord ++ tailWord_1440071).sum := by decide
  have hdescent : baseEnd_1440071 < baseStart_1440071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440178 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_1440178 : Nat := 118140960795 + 1440178 * 2 ^ 59
def prefixEnd_1440178 : Nat := 4983230072969 + 3 ^ 40 * 1440178 * 2
def baseEnd_1440178 : Nat := 328668240902654013622999

theorem tailTrace_1440178 : CollatzResearch.WordTrace tailWord_1440178 prefixEnd_1440178 328668240902654013622999 := by
  unfold tailWord_1440178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13131901744122135916352297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35018404650992362443606125 13131901744122135916352297)
  ·
    refine ⟨9848926308091601937264223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13131901744122135916352297 9848926308091601937264223)
    ·
      refine ⟨14773389462137402905896335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9848926308091601937264223 14773389462137402905896335)
      ·
        refine ⟨22160084193206104358844503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14773389462137402905896335 22160084193206104358844503)
        ·
          refine ⟨33240126289809156538266755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22160084193206104358844503 33240126289809156538266755)
          ·
            refine ⟨49860189434713734807400133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33240126289809156538266755 49860189434713734807400133)
            ·
              refine ⟨9348785519008825276387525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49860189434713734807400133 9348785519008825276387525)
              ·
                refine ⟨1752897284814154739322661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9348785519008825276387525 1752897284814154739322661)
                ·
                  refine ⟨328668240902654013622999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1752897284814154739322661 328668240902654013622999)
                  ·
                    rfl

theorem cell21_1440178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_1440178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440178 prefixEnd_1440178 := by exact prefixLift 1440178
  have htrace : WordTrace (prefixWord ++ tailWord_1440178) baseStart_1440178 baseEnd_1440178 := by
    simpa [prefixWord, tailWord_1440178, baseEnd_1440178] using wordTrace_append hprefix tailTrace_1440178
  have hstable : (prefixWord ++ tailWord_1440178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440178).length < 2 ^ (prefixWord ++ tailWord_1440178).sum := by decide
  have hdescent : baseEnd_1440178 < baseStart_1440178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440181 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 5]
def baseStart_1440181 : Nat := 118140960795 + 1440181 * 2 ^ 59
def prefixEnd_1440181 : Nat := 4983230072969 + 3 ^ 40 * 1440181 * 2
def baseEnd_1440181 : Nat := 328668925543526675072993

theorem tailTrace_1440181 : CollatzResearch.WordTrace tailWord_1440181 prefixEnd_1440181 328668925543526675072993 := by
  unfold tailWord_1440181
  simp only [CollatzResearch.WordTrace]
  refine ⟨52527716395477675177768397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35018477596985116785178931 52527716395477675177768397)
  ·
    refine ⟨19697893648304128191663149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52527716395477675177768397 19697893648304128191663149)
    ·
      refine ⟨7386710118114048071873681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19697893648304128191663149 7386710118114048071873681)
      ·
        refine ⟨5540032588585536053905261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7386710118114048071873681 5540032588585536053905261)
        ·
          refine ⟨2077512220719576020214473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5540032588585536053905261 2077512220719576020214473)
          ·
            refine ⟨1558134165539682015160855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2077512220719576020214473 1558134165539682015160855)
            ·
              refine ⟨2337201248309523022741283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558134165539682015160855 2337201248309523022741283)
              ·
                refine ⟨3505801872464284534111925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2337201248309523022741283 3505801872464284534111925)
                ·
                  refine ⟨328668925543526675072993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3505801872464284534111925 328668925543526675072993)
                  ·
                    rfl

theorem cell21_1440181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_1440181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440181 prefixEnd_1440181 := by exact prefixLift 1440181
  have htrace : WordTrace (prefixWord ++ tailWord_1440181) baseStart_1440181 baseEnd_1440181 := by
    simpa [prefixWord, tailWord_1440181, baseEnd_1440181] using wordTrace_append hprefix tailTrace_1440181
  have hstable : (prefixWord ++ tailWord_1440181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440181).length < 2 ^ (prefixWord ++ tailWord_1440181).sum := by decide
  have hdescent : baseEnd_1440181 < baseStart_1440181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440226 : List Nat := [3, 3, 3, 2, 1, 9]
def baseStart_1440226 : Nat := 118140960795 + 1440226 * 2 ^ 59
def prefixEnd_1440226 : Nat := 4983230072969 + 3 ^ 40 * 1440226 * 2
def baseEnd_1440226 : Nat := 12173303524319133215663

theorem tailTrace_1440226 : CollatzResearch.WordTrace tailWord_1440226 prefixEnd_1440226 12173303524319133215663 := by
  unfold tailWord_1440226
  simp only [CollatzResearch.WordTrace]
  refine ⟨13132339420078661965789133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35019571786876431908771021 13132339420078661965789133)
  ·
    refine ⟨4924627282529498237170925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13132339420078661965789133 4924627282529498237170925)
    ·
      refine ⟨1846735230948561838939097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4924627282529498237170925 1846735230948561838939097)
      ·
        refine ⟨1385051423211421379204323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1846735230948561838939097 1385051423211421379204323)
        ·
          refine ⟨2077577134817132068806485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385051423211421379204323 2077577134817132068806485)
          ·
            refine ⟨12173303524319133215663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2077577134817132068806485 12173303524319133215663)
            ·
              rfl

theorem cell21_1440226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 9].length) (baseStart_1440226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440226 prefixEnd_1440226 := by exact prefixLift 1440226
  have htrace : WordTrace (prefixWord ++ tailWord_1440226) baseStart_1440226 baseEnd_1440226 := by
    simpa [prefixWord, tailWord_1440226, baseEnd_1440226] using wordTrace_append hprefix tailTrace_1440226
  have hstable : (prefixWord ++ tailWord_1440226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440226).length < 2 ^ (prefixWord ++ tailWord_1440226).sum := by decide
  have hdescent : baseEnd_1440226 < baseStart_1440226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440240 : List Nat := [2, 1, 1, 1, 3, 3, 3, 4, 3]
def baseStart_1440240 : Nat := 118140960795 + 1440240 * 2 ^ 59
def prefixEnd_1440240 : Nat := 4983230072969 + 3 ^ 40 * 1440240 * 2
def baseEnd_1440240 : Nat := 328682390147355683589539

theorem tailTrace_1440240 : CollatzResearch.WordTrace tailWord_1440240 prefixEnd_1440240 328682390147355683589539 := by
  unfold tailWord_1440240
  simp only [CollatzResearch.WordTrace]
  refine ⟨26264934151131964127083087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35019912201509285502777449 26264934151131964127083087)
  ·
    refine ⟨39397401226697946190624631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26264934151131964127083087 39397401226697946190624631)
    ·
      refine ⟨59096101840046919285936947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39397401226697946190624631 59096101840046919285936947)
      ·
        refine ⟨88644152760070378928905421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59096101840046919285936947 88644152760070378928905421)
        ·
          refine ⟨33241557285026392098339533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88644152760070378928905421 33241557285026392098339533)
          ·
            refine ⟨12465583981884897036877325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33241557285026392098339533 12465583981884897036877325)
            ·
              refine ⟨4674593993206836388828997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12465583981884897036877325 4674593993206836388828997)
              ·
                refine ⟨876486373726281822905437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4674593993206836388828997 876486373726281822905437)
                ·
                  refine ⟨328682390147355683589539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 876486373726281822905437 328682390147355683589539)
                  ·
                    rfl

theorem cell21_1440240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 3].length) (baseStart_1440240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440240 prefixEnd_1440240 := by exact prefixLift 1440240
  have htrace : WordTrace (prefixWord ++ tailWord_1440240) baseStart_1440240 baseEnd_1440240 := by
    simpa [prefixWord, tailWord_1440240, baseEnd_1440240] using wordTrace_append hprefix tailTrace_1440240
  have hstable : (prefixWord ++ tailWord_1440240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440240).length < 2 ^ (prefixWord ++ tailWord_1440240).sum := by decide
  have hdescent : baseEnd_1440240 < baseStart_1440240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440288 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 4]
def baseStart_1440288 : Nat := 118140960795 + 1440288 * 2 ^ 59
def prefixEnd_1440288 : Nat := 4983230072969 + 3 ^ 40 * 1440288 * 2
def baseEnd_1440288 : Nat := 328693344401318266789441

theorem tailTrace_1440288 : CollatzResearch.WordTrace tailWord_1440288 prefixEnd_1440288 328693344401318266789441 := by
  unfold tailWord_1440288
  simp only [CollatzResearch.WordTrace]
  refine ⟨26265809503045016225956759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35021079337393354967942345 26265809503045016225956759)
  ·
    refine ⟨39398714254567524338935139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26265809503045016225956759 39398714254567524338935139)
    ·
      refine ⟨59098071381851286508402709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39398714254567524338935139 59098071381851286508402709)
      ·
        refine ⟨2770222096024279055081377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59098071381851286508402709 2770222096024279055081377)
        ·
          refine ⟨2077666572018209291311033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2770222096024279055081377 2077666572018209291311033)
          ·
            refine ⟨1558249929013656968483275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2077666572018209291311033 1558249929013656968483275)
            ·
              refine ⟨2337374893520485452724913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558249929013656968483275 2337374893520485452724913)
              ·
                refine ⟨1753031170140364089543685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337374893520485452724913 1753031170140364089543685)
                ·
                  refine ⟨328693344401318266789441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753031170140364089543685 328693344401318266789441)
                  ·
                    rfl

theorem cell21_1440288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_1440288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440288 prefixEnd_1440288 := by exact prefixLift 1440288
  have htrace : WordTrace (prefixWord ++ tailWord_1440288) baseStart_1440288 baseEnd_1440288 := by
    simpa [prefixWord, tailWord_1440288, baseEnd_1440288] using wordTrace_append hprefix tailTrace_1440288
  have hstable : (prefixWord ++ tailWord_1440288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440288).length < 2 ^ (prefixWord ++ tailWord_1440288).sum := by decide
  have hdescent : baseEnd_1440288 < baseStart_1440288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440465 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 6]
def baseStart_1440465 : Nat := 118140960795 + 1440465 * 2 ^ 59
def prefixEnd_1440465 : Nat := 4983230072969 + 3 ^ 40 * 1440465 * 2
def baseEnd_1440465 : Nat := 328733738212805292339079

theorem tailTrace_1440465 : CollatzResearch.WordTrace tailWord_1440465 prefixEnd_1440465 328733738212805292339079 := by
  unfold tailWord_1440465
  simp only [CollatzResearch.WordTrace]
  refine ⟨52538074726448791681106849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35025383150965861120737899 52538074726448791681106849)
  ·
    refine ⟨39403556044836593760830137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52538074726448791681106849 39403556044836593760830137)
    ·
      refine ⟨29552667033627445320622603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39403556044836593760830137 29552667033627445320622603)
      ·
        refine ⟨44329000550441167980933905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29552667033627445320622603 44329000550441167980933905)
        ·
          refine ⟨33246750412830875985700429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44329000550441167980933905 33246750412830875985700429)
          ·
            refine ⟨12467531404811578494637661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33246750412830875985700429 12467531404811578494637661)
            ·
              refine ⟨4675324276804341935489123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12467531404811578494637661 4675324276804341935489123)
              ·
                refine ⟨7012986415206512903233685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675324276804341935489123 7012986415206512903233685)
                ·
                  refine ⟨328733738212805292339079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7012986415206512903233685 328733738212805292339079)
                  ·
                    rfl

theorem cell21_1440465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_1440465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440465 prefixEnd_1440465 := by exact prefixLift 1440465
  have htrace : WordTrace (prefixWord ++ tailWord_1440465) baseStart_1440465 baseEnd_1440465 := by
    simpa [prefixWord, tailWord_1440465, baseEnd_1440465] using wordTrace_append hprefix tailTrace_1440465
  have hstable : (prefixWord ++ tailWord_1440465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440465).length < 2 ^ (prefixWord ++ tailWord_1440465).sum := by decide
  have hdescent : baseEnd_1440465 < baseStart_1440465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440530 : List Nat := [3, 2, 4, 1, 2, 1, 2, 6]
def baseStart_1440530 : Nat := 118140960795 + 1440530 * 2 ^ 59
def prefixEnd_1440530 : Nat := 4983230072969 + 3 ^ 40 * 1440530 * 2
def baseEnd_1440530 : Nat := 109582857366126541251871

theorem tailTrace_1440530 : CollatzResearch.WordTrace tailWord_1440530 prefixEnd_1440530 109582857366126541251871 := by
  unfold tailWord_1440530
  simp only [CollatzResearch.WordTrace]
  refine ⟨13135111367803326945555761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35026963647475538521482029 13135111367803326945555761)
  ·
    refine ⟨9851333525852495209166821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13135111367803326945555761 9851333525852495209166821)
    ·
      refine ⟨1847125036097342851718779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9851333525852495209166821 1847125036097342851718779)
      ·
        refine ⟨2770687554146014277578169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847125036097342851718779 2770687554146014277578169)
        ·
          refine ⟨2078015665609510708183627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2770687554146014277578169 2078015665609510708183627)
          ·
            refine ⟨3117023498414266062275441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078015665609510708183627 3117023498414266062275441)
            ·
              refine ⟨2337767623810699546706581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3117023498414266062275441 2337767623810699546706581)
              ·
                refine ⟨109582857366126541251871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2337767623810699546706581 109582857366126541251871)
                ·
                  rfl

theorem cell21_1440530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_1440530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440530 prefixEnd_1440530 := by exact prefixLift 1440530
  have htrace : WordTrace (prefixWord ++ tailWord_1440530) baseStart_1440530 baseEnd_1440530 := by
    simpa [prefixWord, tailWord_1440530, baseEnd_1440530] using wordTrace_append hprefix tailTrace_1440530
  have hstable : (prefixWord ++ tailWord_1440530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440530).length < 2 ^ (prefixWord ++ tailWord_1440530).sum := by decide
  have hdescent : baseEnd_1440530 < baseStart_1440530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440620 : List Nat := [2, 2, 1, 1, 4, 1, 4, 3, 3]
def baseStart_1440620 : Nat := 118140960795 + 1440620 * 2 ^ 59
def prefixEnd_1440620 : Nat := 4983230072969 + 3 ^ 40 * 1440620 * 2
def baseEnd_1440620 : Nat := 328769111324559467255429

theorem tailTrace_1440620 : CollatzResearch.WordTrace tailWord_1440620 prefixEnd_1440620 328769111324559467255429 := by
  unfold tailWord_1440620
  simp only [CollatzResearch.WordTrace]
  refine ⟨26271864020443626576499657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35029152027258168768666209 26271864020443626576499657)
  ·
    refine ⟨19703898015332719932374743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26271864020443626576499657 19703898015332719932374743)
    ·
      refine ⟨29555847022999079898562115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19703898015332719932374743 29555847022999079898562115)
      ·
        refine ⟨44333770534498619847843173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29555847022999079898562115 44333770534498619847843173)
        ·
          refine ⟨8312581975218491221470595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44333770534498619847843173 8312581975218491221470595)
          ·
            refine ⟨12468872962827736832205893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8312581975218491221470595 12468872962827736832205893)
            ·
              refine ⟨2337913680530200656038605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12468872962827736832205893 2337913680530200656038605)
              ·
                refine ⟨876717630198825246014477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2337913680530200656038605 876717630198825246014477)
                ·
                  refine ⟨328769111324559467255429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 876717630198825246014477 328769111324559467255429)
                  ·
                    rfl

theorem cell21_1440620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_1440620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440620 prefixEnd_1440620 := by exact prefixLift 1440620
  have htrace : WordTrace (prefixWord ++ tailWord_1440620) baseStart_1440620 baseEnd_1440620 := by
    simpa [prefixWord, tailWord_1440620, baseEnd_1440620] using wordTrace_append hprefix tailTrace_1440620
  have hstable : (prefixWord ++ tailWord_1440620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440620).length < 2 ^ (prefixWord ++ tailWord_1440620).sum := by decide
  have hdescent : baseEnd_1440620 < baseStart_1440620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440693 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 6]
def baseStart_1440693 : Nat := 118140960795 + 1440693 * 2 ^ 59
def prefixEnd_1440693 : Nat := 4983230072969 + 3 ^ 40 * 1440693 * 2
def baseEnd_1440693 : Nat := 328785770919127562538613

theorem tailTrace_1440693 : CollatzResearch.WordTrace tailWord_1440693 prefixEnd_1440693 328785770919127562538613 := by
  unfold tailWord_1440693
  simp only [CollatzResearch.WordTrace]
  refine ⟨52546390569622786620406733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35030927046415191080271155 52546390569622786620406733)
  ·
    refine ⟨19704896463608544982652525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52546390569622786620406733 19704896463608544982652525)
    ·
      refine ⟨7389336173853204368494697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19704896463608544982652525 7389336173853204368494697)
      ·
        refine ⟨5542002130389903276371023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7389336173853204368494697 5542002130389903276371023)
        ·
          refine ⟨8313003195584854914556535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5542002130389903276371023 8313003195584854914556535)
          ·
            refine ⟨12469504793377282371834803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8313003195584854914556535 12469504793377282371834803)
            ·
              refine ⟨18704257190065923557752205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12469504793377282371834803 18704257190065923557752205)
              ·
                refine ⟨7014096446274721334157077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18704257190065923557752205 7014096446274721334157077)
                ·
                  refine ⟨328785770919127562538613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7014096446274721334157077 328785770919127562538613)
                  ·
                    rfl

theorem cell21_1440693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_1440693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440693 prefixEnd_1440693 := by exact prefixLift 1440693
  have htrace : WordTrace (prefixWord ++ tailWord_1440693) baseStart_1440693 baseEnd_1440693 := by
    simpa [prefixWord, tailWord_1440693, baseEnd_1440693] using wordTrace_append hprefix tailTrace_1440693
  have hstable : (prefixWord ++ tailWord_1440693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440693).length < 2 ^ (prefixWord ++ tailWord_1440693).sum := by decide
  have hdescent : baseEnd_1440693 < baseStart_1440693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440724 : List Nat := [2, 4, 1, 2, 1, 2, 2, 7]
def baseStart_1440724 : Nat := 118140960795 + 1440724 * 2 ^ 59
def prefixEnd_1440724 : Nat := 4983230072969 + 3 ^ 40 * 1440724 * 2
def baseEnd_1440724 : Nat := 109597615180492799173961

theorem tailTrace_1440724 : CollatzResearch.WordTrace tailWord_1440724 prefixEnd_1440724 109597615180492799173961 := by
  unfold tailWord_1440724
  simp only [CollatzResearch.WordTrace]
  refine ⟨26273760616255239457392613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35031680821673652609856817 26273760616255239457392613)
  ·
    refine ⟨4926330115547857398261115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26273760616255239457392613 4926330115547857398261115)
    ·
      refine ⟨7389495173321786097391673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4926330115547857398261115 7389495173321786097391673)
      ·
        refine ⟨5542121379991339573043755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7389495173321786097391673 5542121379991339573043755)
        ·
          refine ⟨8313182069987009359565633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5542121379991339573043755 8313182069987009359565633)
          ·
            refine ⟨6234886552490257019674225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8313182069987009359565633 6234886552490257019674225)
            ·
              refine ⟨4676164914367692764755669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6234886552490257019674225 4676164914367692764755669)
              ·
                refine ⟨109597615180492799173961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4676164914367692764755669 109597615180492799173961)
                ·
                  rfl

theorem cell21_1440724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_1440724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440724 prefixEnd_1440724 := by exact prefixLift 1440724
  have htrace : WordTrace (prefixWord ++ tailWord_1440724) baseStart_1440724 baseEnd_1440724 := by
    simpa [prefixWord, tailWord_1440724, baseEnd_1440724] using wordTrace_append hprefix tailTrace_1440724
  have hstable : (prefixWord ++ tailWord_1440724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440724).length < 2 ^ (prefixWord ++ tailWord_1440724).sum := by decide
  have hdescent : baseEnd_1440724 < baseStart_1440724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440741 : List Nat := [1, 3, 1, 6, 2, 8]
def baseStart_1440741 : Nat := 118140960795 + 1440741 * 2 ^ 59
def prefixEnd_1440741 : Nat := 4983230072969 + 3 ^ 40 * 1440741 * 2
def baseEnd_1440741 : Nat := 12177656487892227619945

theorem tailTrace_1440741 : CollatzResearch.WordTrace tailWord_1440741 prefixEnd_1440741 12177656487892227619945 := by
  unfold tailWord_1440741
  simp only [CollatzResearch.WordTrace]
  refine ⟨52548141273448890818154077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35032094182299260545436051 52548141273448890818154077)
  ·
    refine ⟨19705552977543334056807779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52548141273448890818154077 19705552977543334056807779)
    ·
      refine ⟨29558329466315001085211669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19705552977543334056807779 29558329466315001085211669)
      ·
        refine ⟨1385546693733515675869297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29558329466315001085211669 1385546693733515675869297)
        ·
          refine ⟨1039160020300136756901973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1385546693733515675869297 1039160020300136756901973)
          ·
            refine ⟨12177656487892227619945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1039160020300136756901973 12177656487892227619945)
            ·
              rfl

theorem cell21_1440741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 8].length) (baseStart_1440741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440741 prefixEnd_1440741 := by exact prefixLift 1440741
  have htrace : WordTrace (prefixWord ++ tailWord_1440741) baseStart_1440741 baseEnd_1440741 := by
    simpa [prefixWord, tailWord_1440741, baseEnd_1440741] using wordTrace_append hprefix tailTrace_1440741
  have hstable : (prefixWord ++ tailWord_1440741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440741).length < 2 ^ (prefixWord ++ tailWord_1440741).sum := by decide
  have hdescent : baseEnd_1440741 < baseStart_1440741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440820 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1440820 : Nat := 118140960795 + 1440820 * 2 ^ 59
def prefixEnd_1440820 : Nat := 4983230072969 + 3 ^ 40 * 1440820 * 2
def baseEnd_1440820 : Nat := 328814754049403563921687

theorem tailTrace_1440820 : CollatzResearch.WordTrace tailWord_1440820 prefixEnd_1440820 328814754049403563921687 := by
  unfold tailWord_1440820
  simp only [CollatzResearch.WordTrace]
  refine ⟨26275511320081343655139957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35034015093441791540186609 26275511320081343655139957)
  ·
    refine ⟨2463329186257625967669371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26275511320081343655139957 2463329186257625967669371)
    ·
      refine ⟨3694993779386438951504057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2463329186257625967669371 3694993779386438951504057)
      ·
        refine ⟨2771245334539829213628043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3694993779386438951504057 2771245334539829213628043)
        ·
          refine ⟨4156868001809743820442065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2771245334539829213628043 4156868001809743820442065)
          ·
            refine ⟨3117651001357307865331549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4156868001809743820442065 3117651001357307865331549)
            ·
              refine ⟨1169119125508990449499331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3117651001357307865331549 1169119125508990449499331)
              ·
                refine ⟨1753678688263485674248997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169119125508990449499331 1753678688263485674248997)
                ·
                  refine ⟨328814754049403563921687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753678688263485674248997 328814754049403563921687)
                  ·
                    rfl

theorem cell21_1440820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1440820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440820 prefixEnd_1440820 := by exact prefixLift 1440820
  have htrace : WordTrace (prefixWord ++ tailWord_1440820) baseStart_1440820 baseEnd_1440820 := by
    simpa [prefixWord, tailWord_1440820, baseEnd_1440820] using wordTrace_append hprefix tailTrace_1440820
  have hstable : (prefixWord ++ tailWord_1440820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440820).length < 2 ^ (prefixWord ++ tailWord_1440820).sum := by decide
  have hdescent : baseEnd_1440820 < baseStart_1440820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440924 : List Nat := [2, 2, 3, 2, 1, 3, 1, 4, 3]
def baseStart_1440924 : Nat := 118140960795 + 1440924 * 2 ^ 59
def prefixEnd_1440924 : Nat := 4983230072969 + 3 ^ 40 * 1440924 * 2
def baseEnd_1440924 : Nat := 328838488266322494188141

theorem tailTrace_1440924 : CollatzResearch.WordTrace tailWord_1440924 prefixEnd_1440924 328838488266322494188141 := by
  unfold tailWord_1440924
  simp only [CollatzResearch.WordTrace]
  refine ⟨26277407915892956536032913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35036543887857275381377217 26277407915892956536032913)
  ·
    refine ⟨19708055936919717402024685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26277407915892956536032913 19708055936919717402024685)
    ·
      refine ⟨7390520976344894025759257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19708055936919717402024685 7390520976344894025759257)
      ·
        refine ⟨5542890732258670519319443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7390520976344894025759257 5542890732258670519319443)
        ·
          refine ⟨8314336098388005778979165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5542890732258670519319443 8314336098388005778979165)
          ·
            refine ⟨3117876036895502167117187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8314336098388005778979165 3117876036895502167117187)
            ·
              refine ⟨4676814055343253250675781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117876036895502167117187 4676814055343253250675781)
              ·
                refine ⟨876902635376859984501709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4676814055343253250675781 876902635376859984501709)
                ·
                  refine ⟨328838488266322494188141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 876902635376859984501709 328838488266322494188141)
                  ·
                    rfl

theorem cell21_1440924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_1440924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440924 prefixEnd_1440924 := by exact prefixLift 1440924
  have htrace : WordTrace (prefixWord ++ tailWord_1440924) baseStart_1440924 baseEnd_1440924 := by
    simpa [prefixWord, tailWord_1440924, baseEnd_1440924] using wordTrace_append hprefix tailTrace_1440924
  have hstable : (prefixWord ++ tailWord_1440924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440924).length < 2 ^ (prefixWord ++ tailWord_1440924).sum := by decide
  have hdescent : baseEnd_1440924 < baseStart_1440924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440983 : List Nat := [1, 1, 3, 2, 1, 2, 4, 4, 3]
def baseStart_1440983 : Nat := 118140960795 + 1440983 * 2 ^ 59
def prefixEnd_1440983 : Nat := 4983230072969 + 3 ^ 40 * 1440983 * 2
def baseEnd_1440983 : Nat := 328851952870151502704687

theorem tailTrace_1440983 : CollatzResearch.WordTrace tailWord_1440983 prefixEnd_1440983 328851952870151502704687 := by
  unfold tailWord_1440983
  simp only [CollatzResearch.WordTrace]
  refine ⟨52556967738572166148463603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35037978492381444098975735 52556967738572166148463603)
  ·
    refine ⟨78835451607858249222695405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52556967738572166148463603 78835451607858249222695405)
    ·
      refine ⟨29563294352946843458510777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78835451607858249222695405 29563294352946843458510777)
      ·
        refine ⟨22172470764710132593883083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29563294352946843458510777 22172470764710132593883083)
        ·
          refine ⟨33258706147065198890824625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22172470764710132593883083 33258706147065198890824625)
          ·
            refine ⟨24944029610298899168118469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33258706147065198890824625 24944029610298899168118469)
            ·
              refine ⟨4677005551931043594022213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24944029610298899168118469 4677005551931043594022213)
              ·
                refine ⟨876938540987070673879165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4677005551931043594022213 876938540987070673879165)
                ·
                  refine ⟨328851952870151502704687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 876938540987070673879165 328851952870151502704687)
                  ·
                    rfl

theorem cell21_1440983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 3].length) (baseStart_1440983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1440983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1440983 prefixEnd_1440983 := by exact prefixLift 1440983
  have htrace : WordTrace (prefixWord ++ tailWord_1440983) baseStart_1440983 baseEnd_1440983 := by
    simpa [prefixWord, tailWord_1440983, baseEnd_1440983] using wordTrace_append hprefix tailTrace_1440983
  have hstable : (prefixWord ++ tailWord_1440983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440983).length < 2 ^ (prefixWord ++ tailWord_1440983).sum := by decide
  have hdescent : baseEnd_1440983 < baseStart_1440983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441011 : List Nat := [1, 1, 1, 2, 2, 6, 1, 7]
def baseStart_1441011 : Nat := 118140960795 + 1441011 * 2 ^ 59
def prefixEnd_1441011 : Nat := 4983230072969 + 3 ^ 40 * 1441011 * 2
def baseEnd_1441011 : Nat := 109619447617209892079321

theorem tailTrace_1441011 : CollatzResearch.WordTrace tailWord_1441011 prefixEnd_1441011 109619447617209892079321 := by
  unfold tailWord_1441011
  simp only [CollatzResearch.WordTrace]
  refine ⟨52557988982470726930482887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35038659321647151286988591 52557988982470726930482887)
  ·
    refine ⟨78836983473706090395724331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52557988982470726930482887 78836983473706090395724331)
    ·
      refine ⟨118255475210559135593586497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78836983473706090395724331 118255475210559135593586497)
      ·
        refine ⟨88691606407919351695189873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118255475210559135593586497 88691606407919351695189873)
        ·
          refine ⟨66518704805939513771392405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88691606407919351695189873 66518704805939513771392405)
          ·
            refine ⟨3118064287778414708034019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66518704805939513771392405 3118064287778414708034019)
            ·
              refine ⟨4677096431667622062051029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118064287778414708034019 4677096431667622062051029)
              ·
                refine ⟨109619447617209892079321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4677096431667622062051029 109619447617209892079321)
                ·
                  rfl

theorem cell21_1441011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 7].length) (baseStart_1441011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441011 prefixEnd_1441011 := by exact prefixLift 1441011
  have htrace : WordTrace (prefixWord ++ tailWord_1441011) baseStart_1441011 baseEnd_1441011 := by
    simpa [prefixWord, tailWord_1441011, baseEnd_1441011] using wordTrace_append hprefix tailTrace_1441011
  have hstable : (prefixWord ++ tailWord_1441011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441011).length < 2 ^ (prefixWord ++ tailWord_1441011).sum := by decide
  have hdescent : baseEnd_1441011 < baseStart_1441011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441028 : List Nat := [2, 3, 2, 2, 2, 3, 7]
def baseStart_1441028 : Nat := 118140960795 + 1441028 * 2 ^ 59
def prefixEnd_1441028 : Nat := 4983230072969 + 3 ^ 40 * 1441028 * 2
def baseEnd_1441028 : Nat := 36540246942582380494955

theorem tailTrace_1441028 : CollatzResearch.WordTrace tailWord_1441028 prefixEnd_1441028 36540246942582380494955 := by
  unfold tailWord_1441028
  simp only [CollatzResearch.WordTrace]
  refine ⟨26279304511704569416925869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35039072682272759222567825 26279304511704569416925869)
  ·
    refine ⟨9854739191889213531347201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26279304511704569416925869 9854739191889213531347201)
    ·
      refine ⟨7391054393916910148510401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9854739191889213531347201 7391054393916910148510401)
      ·
        refine ⟨5543290795437682611382801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7391054393916910148510401 5543290795437682611382801)
        ·
          refine ⟨4157468096578261958537101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5543290795437682611382801 4157468096578261958537101)
          ·
            refine ⟨1559050536216848234451413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4157468096578261958537101 1559050536216848234451413)
            ·
              refine ⟨36540246942582380494955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1559050536216848234451413 36540246942582380494955)
              ·
                rfl

theorem cell21_1441028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 7].length) (baseStart_1441028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441028 prefixEnd_1441028 := by exact prefixLift 1441028
  have htrace : WordTrace (prefixWord ++ tailWord_1441028) baseStart_1441028 baseEnd_1441028 := by
    simpa [prefixWord, tailWord_1441028, baseEnd_1441028] using wordTrace_append hprefix tailTrace_1441028
  have hstable : (prefixWord ++ tailWord_1441028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441028).length < 2 ^ (prefixWord ++ tailWord_1441028).sum := by decide
  have hdescent : baseEnd_1441028 < baseStart_1441028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441076 : List Nat := [2, 5, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1441076 : Nat := 118140960795 + 1441076 * 2 ^ 59
def prefixEnd_1441076 : Nat := 4983230072969 + 3 ^ 40 * 1441076 * 2
def baseEnd_1441076 : Nat := 328873176737204007654497

theorem tailTrace_1441076 : CollatzResearch.WordTrace tailWord_1441076 prefixEnd_1441076 328873176737204007654497 := by
  unfold tailWord_1441076
  simp only [CollatzResearch.WordTrace]
  refine ⟨26280179863617621515799541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35040239818156828687732721 26280179863617621515799541)
  ·
    refine ⟨2463766862214152017106207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26280179863617621515799541 2463766862214152017106207)
    ·
      refine ⟨3695650293321228025659311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2463766862214152017106207 3695650293321228025659311)
      ·
        refine ⟨5543475439981842038488967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3695650293321228025659311 5543475439981842038488967)
        ·
          refine ⟨8315213159972763057733451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5543475439981842038488967 8315213159972763057733451)
          ·
            refine ⟨12472819739959144586600177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8315213159972763057733451 12472819739959144586600177)
            ·
              refine ⟨9354614804969358439950133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12472819739959144586600177 9354614804969358439950133)
              ·
                refine ⟨876995137965877353745325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9354614804969358439950133 876995137965877353745325)
                ·
                  refine ⟨328873176737204007654497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 876995137965877353745325 328873176737204007654497)
                  ·
                    rfl

theorem cell21_1441076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1441076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441076 prefixEnd_1441076 := by exact prefixLift 1441076
  have htrace : WordTrace (prefixWord ++ tailWord_1441076) baseStart_1441076 baseEnd_1441076 := by
    simpa [prefixWord, tailWord_1441076, baseEnd_1441076] using wordTrace_append hprefix tailTrace_1441076
  have hstable : (prefixWord ++ tailWord_1441076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441076).length < 2 ^ (prefixWord ++ tailWord_1441076).sum := by decide
  have hdescent : baseEnd_1441076 < baseStart_1441076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441110 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1441110 : Nat := 118140960795 + 1441110 * 2 ^ 59
def prefixEnd_1441110 : Nat := 4983230072969 + 3 ^ 40 * 1441110 * 2
def baseEnd_1441110 : Nat := 328880936000427504087761

theorem tailTrace_1441110 : CollatzResearch.WordTrace tailWord_1441110 prefixEnd_1441110 328880936000427504087761 := by
  unfold tailWord_1441110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3285099988069504177396049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35041066539408044558891189 3285099988069504177396049)
  ·
    refine ⟨2463824991052128133047037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3285099988069504177396049 2463824991052128133047037)
    ·
      refine ⟨923934371644548049892639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2463824991052128133047037 923934371644548049892639)
      ·
        refine ⟨1385901557466822074838959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923934371644548049892639 1385901557466822074838959)
        ·
          refine ⟨2078852336200233112258439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385901557466822074838959 2078852336200233112258439)
          ·
            refine ⟨3118278504300349668387659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078852336200233112258439 3118278504300349668387659)
            ·
              refine ⟨4677417756450524502581489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118278504300349668387659 4677417756450524502581489)
              ·
                refine ⟨3508063317337893376936117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4677417756450524502581489 3508063317337893376936117)
                ·
                  refine ⟨328880936000427504087761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3508063317337893376936117 328880936000427504087761)
                  ·
                    rfl

theorem cell21_1441110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1441110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441110 prefixEnd_1441110 := by exact prefixLift 1441110
  have htrace : WordTrace (prefixWord ++ tailWord_1441110) baseStart_1441110 baseEnd_1441110 := by
    simpa [prefixWord, tailWord_1441110, baseEnd_1441110] using wordTrace_append hprefix tailTrace_1441110
  have hstable : (prefixWord ++ tailWord_1441110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441110).length < 2 ^ (prefixWord ++ tailWord_1441110).sum := by decide
  have hdescent : baseEnd_1441110 < baseStart_1441110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441135 : List Nat := [1, 1, 2, 1, 3, 1, 6, 3, 3]
def baseStart_1441135 : Nat := 118140960795 + 1441135 * 2 ^ 59
def prefixEnd_1441135 : Nat := 4983230072969 + 3 ^ 40 * 1441135 * 2
def baseEnd_1441135 : Nat := 328886641341033016171043

theorem tailTrace_1441135 : CollatzResearch.WordTrace tailWord_1441135 prefixEnd_1441135 328886641341033016171043 := by
  unfold tailWord_1441135
  simp only [CollatzResearch.WordTrace]
  refine ⟨52562511634021496107996859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35041674422680997405331239 52562511634021496107996859)
  ·
    refine ⟨78843767451032244161995289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52562511634021496107996859 78843767451032244161995289)
    ·
      refine ⟨59132825588274183121496467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78843767451032244161995289 59132825588274183121496467)
      ·
        refine ⟨88699238382411274682244701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59132825588274183121496467 88699238382411274682244701)
        ·
          refine ⟨33262214393404228005841763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88699238382411274682244701 33262214393404228005841763)
          ·
            refine ⟨49893321590106342008762645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33262214393404228005841763 49893321590106342008762645)
            ·
              refine ⟨2338749449536234781660749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49893321590106342008762645 2338749449536234781660749)
              ·
                refine ⟨877031043576088043122781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2338749449536234781660749 877031043576088043122781)
                ·
                  refine ⟨328886641341033016171043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877031043576088043122781 328886641341033016171043)
                  ·
                    rfl

theorem cell21_1441135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 3].length) (baseStart_1441135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441135 prefixEnd_1441135 := by exact prefixLift 1441135
  have htrace : WordTrace (prefixWord ++ tailWord_1441135) baseStart_1441135 baseEnd_1441135 := by
    simpa [prefixWord, tailWord_1441135, baseEnd_1441135] using wordTrace_append hprefix tailTrace_1441135
  have hstable : (prefixWord ++ tailWord_1441135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441135).length < 2 ^ (prefixWord ++ tailWord_1441135).sum := by decide
  have hdescent : baseEnd_1441135 < baseStart_1441135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441208 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_1441208 : Nat := 118140960795 + 1441208 * 2 ^ 59
def prefixEnd_1441208 : Nat := 4983230072969 + 3 ^ 40 * 1441208 * 2
def baseEnd_1441208 : Nat := 328903300935601111454227

theorem tailTrace_1441208 : CollatzResearch.WordTrace tailWord_1441208 prefixEnd_1441208 328903300935601111454227 := by
  unfold tailWord_1441208
  simp only [CollatzResearch.WordTrace]
  refine ⟨26282587081378514787702139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35043449441838019716936185 26282587081378514787702139)
  ·
    refine ⟨39423880622067772181553209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26282587081378514787702139 39423880622067772181553209)
    ·
      refine ⟨29567910466550829136164907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39423880622067772181553209 29567910466550829136164907)
      ·
        refine ⟨44351865699826243704247361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29567910466550829136164907 44351865699826243704247361)
        ·
          refine ⟨33263899274869682778185521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44351865699826243704247361 33263899274869682778185521)
          ·
            refine ⟨24947924456152262083639141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33263899274869682778185521 24947924456152262083639141)
            ·
              refine ⟨4677735835528549140682339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24947924456152262083639141 4677735835528549140682339)
              ·
                refine ⟨7016603753292823711023509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4677735835528549140682339 7016603753292823711023509)
                ·
                  refine ⟨328903300935601111454227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7016603753292823711023509 328903300935601111454227)
                  ·
                    rfl

theorem cell21_1441208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_1441208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441208 prefixEnd_1441208 := by exact prefixLift 1441208
  have htrace : WordTrace (prefixWord ++ tailWord_1441208) baseStart_1441208 baseEnd_1441208 := by
    simpa [prefixWord, tailWord_1441208, baseEnd_1441208] using wordTrace_append hprefix tailTrace_1441208
  have hstable : (prefixWord ++ tailWord_1441208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441208).length < 2 ^ (prefixWord ++ tailWord_1441208).sum := by decide
  have hdescent : baseEnd_1441208 < baseStart_1441208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441304 : List Nat := [2, 1, 2, 3, 4, 1, 2, 3, 3]
def baseStart_1441304 : Nat := 118140960795 + 1441304 * 2 ^ 59
def prefixEnd_1441304 : Nat := 4983230072969 + 3 ^ 40 * 1441304 * 2
def baseEnd_1441304 : Nat := 328925209443526277854031

theorem tailTrace_1441304 : CollatzResearch.WordTrace tailWord_1441304 prefixEnd_1441304 328925209443526277854031 := by
  unfold tailWord_1441304
  simp only [CollatzResearch.WordTrace]
  refine ⟨26284337785204618985449483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35045783713606158647265977 26284337785204618985449483)
  ·
    refine ⟨39426506677806928478174225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26284337785204618985449483 39426506677806928478174225)
    ·
      refine ⟨29569880008355196358630669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39426506677806928478174225 29569880008355196358630669)
      ·
        refine ⟨11088705003133198634486501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29569880008355196358630669 11088705003133198634486501)
        ·
          refine ⟨2079132188087474743966219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11088705003133198634486501 2079132188087474743966219)
          ·
            refine ⟨3118698282131212115949329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079132188087474743966219 3118698282131212115949329)
            ·
              refine ⟨2339023711598409086961997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3118698282131212115949329 2339023711598409086961997)
              ·
                refine ⟨877133891849403407610749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2339023711598409086961997 877133891849403407610749)
                ·
                  refine ⟨328925209443526277854031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877133891849403407610749 328925209443526277854031)
                  ·
                    rfl

theorem cell21_1441304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 3].length) (baseStart_1441304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441304 prefixEnd_1441304 := by exact prefixLift 1441304
  have htrace : WordTrace (prefixWord ++ tailWord_1441304) baseStart_1441304 baseEnd_1441304 := by
    simpa [prefixWord, tailWord_1441304, baseEnd_1441304] using wordTrace_append hprefix tailTrace_1441304
  have hstable : (prefixWord ++ tailWord_1441304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441304).length < 2 ^ (prefixWord ++ tailWord_1441304).sum := by decide
  have hdescent : baseEnd_1441304 < baseStart_1441304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441310 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_1441310 : Nat := 118140960795 + 1441310 * 2 ^ 59
def prefixEnd_1441310 : Nat := 4983230072969 + 3 ^ 40 * 1441310 * 2
def baseEnd_1441310 : Nat := 328926578725271600754019

theorem tailTrace_1441310 : CollatzResearch.WordTrace tailWord_1441310 prefixEnd_1441310 328926578725271600754019 := by
  unfold tailWord_1441310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571111801048437624452173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35045929605591667330411589 6571111801048437624452173)
  ·
    refine ⟨2464166925393164109169565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6571111801048437624452173 2464166925393164109169565)
    ·
      refine ⟨924062597022436540938587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2464166925393164109169565 924062597022436540938587)
      ·
        refine ⟨1386093895533654811407881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924062597022436540938587 1386093895533654811407881)
        ·
          refine ⟨1039570421650241108555911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1386093895533654811407881 1039570421650241108555911)
          ·
            refine ⟨1559355632475361662833867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039570421650241108555911 1559355632475361662833867)
            ·
              refine ⟨2339033448713042494250801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559355632475361662833867 2339033448713042494250801)
              ·
                refine ⟨1754275086534781870688101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2339033448713042494250801 1754275086534781870688101)
                ·
                  refine ⟨328926578725271600754019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1754275086534781870688101 328926578725271600754019)
                  ·
                    rfl

theorem cell21_1441310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_1441310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441310 prefixEnd_1441310 := by exact prefixLift 1441310
  have htrace : WordTrace (prefixWord ++ tailWord_1441310) baseStart_1441310 baseEnd_1441310 := by
    simpa [prefixWord, tailWord_1441310, baseEnd_1441310] using wordTrace_append hprefix tailTrace_1441310
  have hstable : (prefixWord ++ tailWord_1441310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441310).length < 2 ^ (prefixWord ++ tailWord_1441310).sum := by decide
  have hdescent : baseEnd_1441310 < baseStart_1441310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441315 : List Nat := [1, 1, 1, 4, 5, 1, 8]
def baseStart_1441315 : Nat := 118140960795 + 1441315 * 2 ^ 59
def prefixEnd_1441315 : Nat := 4983230072969 + 3 ^ 40 * 1441315 * 2
def baseEnd_1441315 : Nat := 36547524421488078130075

theorem tailTrace_1441315 : CollatzResearch.WordTrace tailWord_1441315 prefixEnd_1441315 36547524421488078130075 := by
  unfold tailWord_1441315
  simp only [CollatzResearch.WordTrace]
  refine ⟨52569076773369386849549399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35046051182246257899699599 52569076773369386849549399)
  ·
    refine ⟨78853615160054080274324099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52569076773369386849549399 78853615160054080274324099)
    ·
      refine ⟨118280422740081120411486149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78853615160054080274324099 118280422740081120411486149)
      ·
        refine ⟨22177579263765210077153653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118280422740081120411486149 22177579263765210077153653)
        ·
          refine ⟨2079148055977988444733155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22177579263765210077153653 2079148055977988444733155)
          ·
            refine ⟨3118722083966982667099733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079148055977988444733155 3118722083966982667099733)
            ·
              refine ⟨36547524421488078130075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3118722083966982667099733 36547524421488078130075)
              ·
                rfl

theorem cell21_1441315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 8].length) (baseStart_1441315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441315 prefixEnd_1441315 := by exact prefixLift 1441315
  have htrace : WordTrace (prefixWord ++ tailWord_1441315) baseStart_1441315 baseEnd_1441315 := by
    simpa [prefixWord, tailWord_1441315, baseEnd_1441315] using wordTrace_append hprefix tailTrace_1441315
  have hstable : (prefixWord ++ tailWord_1441315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441315).length < 2 ^ (prefixWord ++ tailWord_1441315).sum := by decide
  have hdescent : baseEnd_1441315 < baseStart_1441315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441366 : List Nat := [5, 2, 2, 2, 1, 2, 7]
def baseStart_1441366 : Nat := 118140960795 + 1441366 * 2 ^ 59
def prefixEnd_1441366 : Nat := 4983230072969 + 3 ^ 40 * 1441366 * 2
def baseEnd_1441366 : Nat := 36548817632025327535619

theorem tailTrace_1441366 : CollatzResearch.WordTrace tailWord_1441366 prefixEnd_1441366 36548817632025327535619 := by
  unfold tailWord_1441366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3285683556011538909978497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35047291264123081706437301 3285683556011538909978497)
  ·
    refine ⟨2464262667008654182483873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3285683556011538909978497 2464262667008654182483873)
    ·
      refine ⟨1848197000256490636862905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2464262667008654182483873 1848197000256490636862905)
      ·
        refine ⟨1386147750192367977647179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1848197000256490636862905 1386147750192367977647179)
        ·
          refine ⟨2079221625288551966470769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386147750192367977647179 2079221625288551966470769)
          ·
            refine ⟨1559416218966413974853077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2079221625288551966470769 1559416218966413974853077)
            ·
              refine ⟨36548817632025327535619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1559416218966413974853077 36548817632025327535619)
              ·
                rfl

theorem cell21_1441366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 7].length) (baseStart_1441366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441366 prefixEnd_1441366 := by exact prefixLift 1441366
  have htrace : WordTrace (prefixWord ++ tailWord_1441366) baseStart_1441366 baseEnd_1441366 := by
    simpa [prefixWord, tailWord_1441366, baseEnd_1441366] using wordTrace_append hprefix tailTrace_1441366
  have hstable : (prefixWord ++ tailWord_1441366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441366).length < 2 ^ (prefixWord ++ tailWord_1441366).sum := by decide
  have hdescent : baseEnd_1441366 < baseStart_1441366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441380 : List Nat := [2, 3, 1, 1, 2, 4, 3, 2, 3]
def baseStart_1441380 : Nat := 118140960795 + 1441380 * 2 ^ 59
def prefixEnd_1441380 : Nat := 4983230072969 + 3 ^ 40 * 1441380 * 2
def baseEnd_1441380 : Nat := 328942553678967034587209

theorem tailTrace_1441380 : CollatzResearch.WordTrace tailWord_1441380 prefixEnd_1441380 328942553678967034587209 := by
  unfold tailWord_1441380
  simp only [CollatzResearch.WordTrace]
  refine ⟨26285723759066951475332797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35047631678755935300443729 26285723759066951475332797)
  ·
    refine ⟨9857146409650106803249799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26285723759066951475332797 9857146409650106803249799)
    ·
      refine ⟨14785719614475160204874699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9857146409650106803249799 14785719614475160204874699)
      ·
        refine ⟨22178579421712740307312049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14785719614475160204874699 22178579421712740307312049)
        ·
          refine ⟨16633934566284555230484037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22178579421712740307312049 16633934566284555230484037)
          ·
            refine ⟨3118862731178354105715757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16633934566284555230484037 3118862731178354105715757)
            ·
              refine ⟨1169573524191882789643409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3118862731178354105715757 1169573524191882789643409)
              ·
                refine ⟨877180143143912092232557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169573524191882789643409 877180143143912092232557)
                ·
                  refine ⟨328942553678967034587209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877180143143912092232557 328942553678967034587209)
                  ·
                    rfl

theorem cell21_1441380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_1441380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441380 prefixEnd_1441380 := by exact prefixLift 1441380
  have htrace : WordTrace (prefixWord ++ tailWord_1441380) baseStart_1441380 baseEnd_1441380 := by
    simpa [prefixWord, tailWord_1441380, baseEnd_1441380] using wordTrace_append hprefix tailTrace_1441380
  have hstable : (prefixWord ++ tailWord_1441380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441380).length < 2 ^ (prefixWord ++ tailWord_1441380).sum := by decide
  have hdescent : baseEnd_1441380 < baseStart_1441380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441394 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_1441394 : Nat := 118140960795 + 1441394 * 2 ^ 59
def prefixEnd_1441394 : Nat := 4983230072969 + 3 ^ 40 * 1441394 * 2
def baseEnd_1441394 : Nat := 328945748669706121353847

theorem tailTrace_1441394 : CollatzResearch.WordTrace tailWord_1441394 prefixEnd_1441394 328945748669706121353847 := by
  unfold tailWord_1441394
  simp only [CollatzResearch.WordTrace]
  refine ⟨13142989535020795835418809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35047972093388788894450157 13142989535020795835418809)
  ·
    refine ⟨9857242151265596876564107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13142989535020795835418809 9857242151265596876564107)
    ·
      refine ⟨14785863226898395314846161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9857242151265596876564107 14785863226898395314846161)
      ·
        refine ⟨11089397420173796486134621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14785863226898395314846161 11089397420173796486134621)
        ·
          refine ⟨4158524032565173682300483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11089397420173796486134621 4158524032565173682300483)
          ·
            refine ⟨6237786048847760523450725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158524032565173682300483 6237786048847760523450725)
            ·
              refine ⟨1169584884158955098147011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6237786048847760523450725 1169584884158955098147011)
              ·
                refine ⟨1754377326238432647220517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169584884158955098147011 1754377326238432647220517)
                ·
                  refine ⟨328945748669706121353847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1754377326238432647220517 328945748669706121353847)
                  ·
                    rfl

theorem cell21_1441394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_1441394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441394 prefixEnd_1441394 := by exact prefixLift 1441394
  have htrace : WordTrace (prefixWord ++ tailWord_1441394) baseStart_1441394 baseEnd_1441394 := by
    simpa [prefixWord, tailWord_1441394, baseEnd_1441394] using wordTrace_append hprefix tailTrace_1441394
  have hstable : (prefixWord ++ tailWord_1441394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441394).length < 2 ^ (prefixWord ++ tailWord_1441394).sum := by decide
  have hdescent : baseEnd_1441394 < baseStart_1441394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441442 : List Nat := [3, 3, 1, 4, 2, 1, 1, 6]
def baseStart_1441442 : Nat := 118140960795 + 1441442 * 2 ^ 59
def prefixEnd_1441442 : Nat := 4983230072969 + 3 ^ 40 * 1441442 * 2
def baseEnd_1441442 : Nat := 109652234307889568184583

theorem tailTrace_1441442 : CollatzResearch.WordTrace tailWord_1441442 prefixEnd_1441442 109652234307889568184583 := by
  unfold tailWord_1441442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13143427210977321884855645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35049139229272858359615053 13143427210977321884855645)
  ·
    refine ⟨4928785204116495706820867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13143427210977321884855645 4928785204116495706820867)
    ·
      refine ⟨7393177806174743560231301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4928785204116495706820867 7393177806174743560231301)
      ·
        refine ⟨1386220838657764417543369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7393177806174743560231301 1386220838657764417543369)
        ·
          refine ⟨1039665628993323313157527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1386220838657764417543369 1039665628993323313157527)
          ·
            refine ⟨1559498443489984969736291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039665628993323313157527 1559498443489984969736291)
            ·
              refine ⟨2339247665234977454604437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559498443489984969736291 2339247665234977454604437)
              ·
                refine ⟨109652234307889568184583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2339247665234977454604437 109652234307889568184583)
                ·
                  rfl

theorem cell21_1441442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_1441442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441442 prefixEnd_1441442 := by exact prefixLift 1441442
  have htrace : WordTrace (prefixWord ++ tailWord_1441442) baseStart_1441442 baseEnd_1441442 := by
    simpa [prefixWord, tailWord_1441442, baseEnd_1441442] using wordTrace_append hprefix tailTrace_1441442
  have hstable : (prefixWord ++ tailWord_1441442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441442).length < 2 ^ (prefixWord ++ tailWord_1441442).sum := by decide
  have hdescent : baseEnd_1441442 < baseStart_1441442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441453 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1441453 : Nat := 118140960795 + 1441453 * 2 ^ 59
def prefixEnd_1441453 : Nat := 4983230072969 + 3 ^ 40 * 1441453 * 2
def baseEnd_1441453 : Nat := 328959213273535129870393

theorem tailTrace_1441453 : CollatzResearch.WordTrace tailWord_1441453 prefixEnd_1441453 328959213273535129870393 := by
  unfold tailWord_1441453
  simp only [CollatzResearch.WordTrace]
  refine ⟨52574110046869436418073013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35049406697912957612048675 52574110046869436418073013)
  ·
    refine ⟨4928822816894009664194345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52574110046869436418073013 4928822816894009664194345)
    ·
      refine ⟨3696617112670507248145759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4928822816894009664194345 3696617112670507248145759)
      ·
        refine ⟨5544925669005760872218639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696617112670507248145759 5544925669005760872218639)
        ·
          refine ⟨8317388503508641308327959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5544925669005760872218639 8317388503508641308327959)
          ·
            refine ⟨12476082755262961962491939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8317388503508641308327959 12476082755262961962491939)
            ·
              refine ⟨18714124132894442943737909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12476082755262961962491939 18714124132894442943737909)
              ·
                refine ⟨1754449137458854025975429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18714124132894442943737909 1754449137458854025975429)
                ·
                  refine ⟨328959213273535129870393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1754449137458854025975429 328959213273535129870393)
                  ·
                    rfl

theorem cell21_1441453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1441453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441453 prefixEnd_1441453 := by exact prefixLift 1441453
  have htrace : WordTrace (prefixWord ++ tailWord_1441453) baseStart_1441453 baseEnd_1441453 := by
    simpa [prefixWord, tailWord_1441453, baseEnd_1441453] using wordTrace_append hprefix tailTrace_1441453
  have hstable : (prefixWord ++ tailWord_1441453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441453).length < 2 ^ (prefixWord ++ tailWord_1441453).sum := by decide
  have hdescent : baseEnd_1441453 < baseStart_1441453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441498 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_1441498 : Nat := 118140960795 + 1441498 * 2 ^ 59
def prefixEnd_1441498 : Nat := 4983230072969 + 3 ^ 40 * 1441498 * 2
def baseEnd_1441498 : Nat := 328969482886625051620301

theorem tailTrace_1441498 : CollatzResearch.WordTrace tailWord_1441498 prefixEnd_1441498 328969482886625051620301 := by
  unfold tailWord_1441498
  simp only [CollatzResearch.WordTrace]
  refine ⟨13143937832926602275865287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35050500887804272735640765 13143937832926602275865287)
  ·
    refine ⟨19715906749389903413797931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13143937832926602275865287 19715906749389903413797931)
    ·
      refine ⟨29573860124084855120696897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19715906749389903413797931 29573860124084855120696897)
      ·
        refine ⟨22180395093063641340522673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29573860124084855120696897 22180395093063641340522673)
        ·
          refine ⟨16635296319797731005392005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22180395093063641340522673 16635296319797731005392005)
          ·
            refine ⟨3119118059962074563511001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16635296319797731005392005 3119118059962074563511001)
            ·
              refine ⟨2339338544971555922633251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3119118059962074563511001 2339338544971555922633251)
              ·
                refine ⟨3509007817457333883949877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339338544971555922633251 3509007817457333883949877)
                ·
                  refine ⟨328969482886625051620301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3509007817457333883949877 328969482886625051620301)
                  ·
                    rfl

theorem cell21_1441498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_1441498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441498 prefixEnd_1441498 := by exact prefixLift 1441498
  have htrace : WordTrace (prefixWord ++ tailWord_1441498) baseStart_1441498 baseEnd_1441498 := by
    simpa [prefixWord, tailWord_1441498, baseEnd_1441498] using wordTrace_append hprefix tailTrace_1441498
  have hstable : (prefixWord ++ tailWord_1441498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441498).length < 2 ^ (prefixWord ++ tailWord_1441498).sum := by decide
  have hdescent : baseEnd_1441498 < baseStart_1441498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441608 : List Nat := [2, 1, 3, 1, 1, 6, 2, 2, 3]
def baseStart_1441608 : Nat := 118140960795 + 1441608 * 2 ^ 59
def prefixEnd_1441608 : Nat := 4983230072969 + 3 ^ 40 * 1441608 * 2
def baseEnd_1441608 : Nat := 328994586385289304786743

theorem tailTrace_1441608 : CollatzResearch.WordTrace tailWord_1441608 prefixEnd_1441608 328994586385289304786743 := by
  unfold tailWord_1441608
  simp only [CollatzResearch.WordTrace]
  refine ⟨26289881680653948944982739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35053175574205265259976985 26289881680653948944982739)
  ·
    refine ⟨39434822520980923417474109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26289881680653948944982739 39434822520980923417474109)
    ·
      refine ⟨14788058445367846281552791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39434822520980923417474109 14788058445367846281552791)
      ·
        refine ⟨22182087668051769422329187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14788058445367846281552791 22182087668051769422329187)
        ·
          refine ⟨33273131502077654133493781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22182087668051769422329187 33273131502077654133493781)
          ·
            refine ⟨1559678039159890037507521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33273131502077654133493781 1559678039159890037507521)
            ·
              refine ⟨1169758529369917528130641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559678039159890037507521 1169758529369917528130641)
              ·
                refine ⟨877318897027438146097981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169758529369917528130641 877318897027438146097981)
                ·
                  refine ⟨328994586385289304786743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877318897027438146097981 328994586385289304786743)
                  ·
                    rfl

theorem cell21_1441608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 3].length) (baseStart_1441608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441608 prefixEnd_1441608 := by exact prefixLift 1441608
  have htrace : WordTrace (prefixWord ++ tailWord_1441608) baseStart_1441608 baseEnd_1441608 := by
    simpa [prefixWord, tailWord_1441608, baseEnd_1441608] using wordTrace_append hprefix tailTrace_1441608
  have hstable : (prefixWord ++ tailWord_1441608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441608).length < 2 ^ (prefixWord ++ tailWord_1441608).sum := by decide
  have hdescent : baseEnd_1441608 < baseStart_1441608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441633 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 5]
def baseStart_1441633 : Nat := 118140960795 + 1441633 * 2 ^ 59
def prefixEnd_1441633 : Nat := 4983230072969 + 3 ^ 40 * 1441633 * 2
def baseEnd_1441633 : Nat := 329000291725894816870025

theorem tailTrace_1441633 : CollatzResearch.WordTrace tailWord_1441633 prefixEnd_1441633 329000291725894816870025 := by
  unfold tailWord_1441633
  simp only [CollatzResearch.WordTrace]
  refine ⟨52580675186217327159625553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35053783457478218106417035 52580675186217327159625553)
  ·
    refine ⟨39435506389662995369719165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52580675186217327159625553 39435506389662995369719165)
    ·
      refine ⟨14788314896123623263644687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39435506389662995369719165 14788314896123623263644687)
      ·
        refine ⟨22182472344185434895467031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14788314896123623263644687 22182472344185434895467031)
        ·
          refine ⟨33273708516278152343200547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22182472344185434895467031 33273708516278152343200547)
          ·
            refine ⟨49910562774417228514800821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33273708516278152343200547 49910562774417228514800821)
            ·
              refine ⟨4679115260101615173262577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49910562774417228514800821 4679115260101615173262577)
              ·
                refine ⟨3509336445076211379946933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4679115260101615173262577 3509336445076211379946933)
                ·
                  refine ⟨329000291725894816870025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3509336445076211379946933 329000291725894816870025)
                  ·
                    rfl

theorem cell21_1441633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_1441633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441633 prefixEnd_1441633 := by exact prefixLift 1441633
  have htrace : WordTrace (prefixWord ++ tailWord_1441633) baseStart_1441633 baseEnd_1441633 := by
    simpa [prefixWord, tailWord_1441633, baseEnd_1441633] using wordTrace_append hprefix tailTrace_1441633
  have hstable : (prefixWord ++ tailWord_1441633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441633).length < 2 ^ (prefixWord ++ tailWord_1441633).sum := by decide
  have hdescent : baseEnd_1441633 < baseStart_1441633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441636 : List Nat := [2, 3, 1, 1, 5, 1, 3, 5]
def baseStart_1441636 : Nat := 118140960795 + 1441636 * 2 ^ 59
def prefixEnd_1441636 : Nat := 4983230072969 + 3 ^ 40 * 1441636 * 2
def baseEnd_1441636 : Nat := 109666992122255826106673

theorem tailTrace_1441636 : CollatzResearch.WordTrace tailWord_1441636 prefixEnd_1441636 109666992122255826106673 := by
  unfold tailWord_1441636
  simp only [CollatzResearch.WordTrace]
  refine ⟨26290392302603229335992381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35053856403470972447989841 26290392302603229335992381)
  ·
    refine ⟨9858897113476211000997143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26290392302603229335992381 9858897113476211000997143)
    ·
      refine ⟨14788345670214316501495715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9858897113476211000997143 14788345670214316501495715)
      ·
        refine ⟨22182518505321474752243573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14788345670214316501495715 22182518505321474752243573)
        ·
          refine ⟨2079611109873888258022835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22182518505321474752243573 2079611109873888258022835)
          ·
            refine ⟨3119416664810832387034253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079611109873888258022835 3119416664810832387034253)
            ·
              refine ⟨1169781249304062145137845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3119416664810832387034253 1169781249304062145137845)
              ·
                refine ⟨109666992122255826106673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1169781249304062145137845 109666992122255826106673)
                ·
                  rfl

theorem cell21_1441636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_1441636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441636 prefixEnd_1441636 := by exact prefixLift 1441636
  have htrace : WordTrace (prefixWord ++ tailWord_1441636) baseStart_1441636 baseEnd_1441636 := by
    simpa [prefixWord, tailWord_1441636, baseEnd_1441636] using wordTrace_append hprefix tailTrace_1441636
  have hstable : (prefixWord ++ tailWord_1441636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441636).length < 2 ^ (prefixWord ++ tailWord_1441636).sum := by decide
  have hdescent : baseEnd_1441636 < baseStart_1441636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441695 : List Nat := [1, 1, 2, 5, 3, 1, 1, 7]
def baseStart_1441695 : Nat := 118140960795 + 1441695 * 2 ^ 59
def prefixEnd_1441695 : Nat := 4983230072969 + 3 ^ 40 * 1441695 * 2
def baseEnd_1441695 : Nat := 109671480323532162278855

theorem tailTrace_1441695 : CollatzResearch.WordTrace tailWord_1441695 prefixEnd_1441695 109671480323532162278855 := by
  unfold tailWord_1441695
  simp only [CollatzResearch.WordTrace]
  refine ⟨52582936511992711748382539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35055291007995141165588359 52582936511992711748382539)
  ·
    refine ⟨78874404767989067622573809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52582936511992711748382539 78874404767989067622573809)
    ·
      refine ⟨59155803575991800716930357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78874404767989067622573809 59155803575991800716930357)
      ·
        refine ⟨5545856585249231317212221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59155803575991800716930357 5545856585249231317212221)
        ·
          refine ⟨2079696219468461743954583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5545856585249231317212221 2079696219468461743954583)
          ·
            refine ⟨3119544329202692615931875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079696219468461743954583 3119544329202692615931875)
            ·
              refine ⟨4679316493804038923897813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119544329202692615931875 4679316493804038923897813)
              ·
                refine ⟨109671480323532162278855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4679316493804038923897813 109671480323532162278855)
                ·
                  rfl

theorem cell21_1441695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 7].length) (baseStart_1441695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441695 prefixEnd_1441695 := by exact prefixLift 1441695
  have htrace : WordTrace (prefixWord ++ tailWord_1441695) baseStart_1441695 baseEnd_1441695 := by
    simpa [prefixWord, tailWord_1441695, baseEnd_1441695] using wordTrace_append hprefix tailTrace_1441695
  have hstable : (prefixWord ++ tailWord_1441695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441695).length < 2 ^ (prefixWord ++ tailWord_1441695).sum := by decide
  have hdescent : baseEnd_1441695 < baseStart_1441695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441726 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_1441726 : Nat := 118140960795 + 1441726 * 2 ^ 59
def prefixEnd_1441726 : Nat := 4983230072969 + 3 ^ 40 * 1441726 * 2
def baseEnd_1441726 : Nat := 329021515592947321819835

theorem tailTrace_1441726 : CollatzResearch.WordTrace tailWord_1441726 prefixEnd_1441726 329021515592947321819835 := by
  unfold tailWord_1441726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573008396860050505345129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35056044783253602695174021 6573008396860050505345129)
  ·
    refine ⟨4929756297645037879008847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6573008396860050505345129 4929756297645037879008847)
    ·
      refine ⟨7394634446467556818513271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4929756297645037879008847 7394634446467556818513271)
      ·
        refine ⟨11091951669701335227769907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7394634446467556818513271 11091951669701335227769907)
        ·
          refine ⟨16637927504552002841654861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11091951669701335227769907 16637927504552002841654861)
          ·
            refine ⟨6239222814207001065620573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16637927504552002841654861 6239222814207001065620573)
            ·
              refine ⟨2339708555327625399607715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6239222814207001065620573 2339708555327625399607715)
              ·
                refine ⟨3509562832991438099411573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339708555327625399607715 3509562832991438099411573)
                ·
                  refine ⟨329021515592947321819835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3509562832991438099411573 329021515592947321819835)
                  ·
                    rfl

theorem cell21_1441726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_1441726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441726 prefixEnd_1441726 := by exact prefixLift 1441726
  have htrace : WordTrace (prefixWord ++ tailWord_1441726) baseStart_1441726 baseEnd_1441726 := by
    simpa [prefixWord, tailWord_1441726, baseEnd_1441726] using wordTrace_append hprefix tailTrace_1441726
  have hstable : (prefixWord ++ tailWord_1441726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441726).length < 2 ^ (prefixWord ++ tailWord_1441726).sum := by decide
  have hdescent : baseEnd_1441726 < baseStart_1441726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441777 : List Nat := [1, 2, 2, 2, 6, 1, 2, 2, 3]
def baseStart_1441777 : Nat := 118140960795 + 1441777 * 2 ^ 59
def prefixEnd_1441777 : Nat := 4983230072969 + 3 ^ 40 * 1441777 * 2
def baseEnd_1441777 : Nat := 329033154487782566469731

theorem tailTrace_1441777 : CollatzResearch.WordTrace tailWord_1441777 prefixEnd_1441777 329033154487782566469731 := by
  unfold tailWord_1441777
  simp only [CollatzResearch.WordTrace]
  refine ⟨52585927297695639752867585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35057284865130426501911723 52585927297695639752867585)
  ·
    refine ⟨39439445473271729814650689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52585927297695639752867585 39439445473271729814650689)
    ·
      refine ⟨29579584104953797360988017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39439445473271729814650689 29579584104953797360988017)
      ·
        refine ⟨22184688078715348020741013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29579584104953797360988017 22184688078715348020741013)
        ·
          refine ⟨1039907253689781938472235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22184688078715348020741013 1039907253689781938472235)
          ·
            refine ⟨1559860880534672907708353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039907253689781938472235 1559860880534672907708353)
            ·
              refine ⟨1169895660401004680781265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559860880534672907708353 1169895660401004680781265)
              ·
                refine ⟨877421745300753510585949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169895660401004680781265 877421745300753510585949)
                ·
                  refine ⟨329033154487782566469731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877421745300753510585949 329033154487782566469731)
                  ·
                    rfl

theorem cell21_1441777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 3].length) (baseStart_1441777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441777 prefixEnd_1441777 := by exact prefixLift 1441777
  have htrace : WordTrace (prefixWord ++ tailWord_1441777) baseStart_1441777 baseEnd_1441777 := by
    simpa [prefixWord, tailWord_1441777, baseEnd_1441777] using wordTrace_append hprefix tailTrace_1441777
  have hstable : (prefixWord ++ tailWord_1441777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441777).length < 2 ^ (prefixWord ++ tailWord_1441777).sum := by decide
  have hdescent : baseEnd_1441777 < baseStart_1441777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441802 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_1441802 : Nat := 118140960795 + 1441802 * 2 ^ 59
def prefixEnd_1441802 : Nat := 4983230072969 + 3 ^ 40 * 1441802 * 2
def baseEnd_1441802 : Nat := 329038859828388078553013

theorem tailTrace_1441802 : CollatzResearch.WordTrace tailWord_1441802 prefixEnd_1441802 329038859828388078553013 := by
  unfold tailWord_1441802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13146709780651267255631915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35057892748403379348351773 13146709780651267255631915)
  ·
    refine ⟨19720064670976900883447873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13146709780651267255631915 19720064670976900883447873)
    ·
      refine ⟨14790048503232675662585905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19720064670976900883447873 14790048503232675662585905)
      ·
        refine ⟨11092536377424506746939429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14790048503232675662585905 11092536377424506746939429)
        ·
          refine ⟨2079850570767095015051143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11092536377424506746939429 2079850570767095015051143)
          ·
            refine ⟨3119775856150642522576715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079850570767095015051143 3119775856150642522576715)
            ·
              refine ⟨4679663784225963783865073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119775856150642522576715 4679663784225963783865073)
              ·
                refine ⟨3509747838169472837898805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4679663784225963783865073 3509747838169472837898805)
                ·
                  refine ⟨329038859828388078553013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3509747838169472837898805 329038859828388078553013)
                  ·
                    rfl

theorem cell21_1441802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_1441802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441802 prefixEnd_1441802 := by exact prefixLift 1441802
  have htrace : WordTrace (prefixWord ++ tailWord_1441802) baseStart_1441802 baseEnd_1441802 := by
    simpa [prefixWord, tailWord_1441802, baseEnd_1441802] using wordTrace_append hprefix tailTrace_1441802
  have hstable : (prefixWord ++ tailWord_1441802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441802).length < 2 ^ (prefixWord ++ tailWord_1441802).sum := by decide
  have hdescent : baseEnd_1441802 < baseStart_1441802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441895 : List Nat := [1, 1, 5, 1, 1, 2, 5, 2, 3]
def baseStart_1441895 : Nat := 118140960795 + 1441895 * 2 ^ 59
def prefixEnd_1441895 : Nat := 4983230072969 + 3 ^ 40 * 1441895 * 2
def baseEnd_1441895 : Nat := 329060083695440583502823

theorem tailTrace_1441895 : CollatzResearch.WordTrace tailWord_1441895 prefixEnd_1441895 329060083695440583502823 := by
  unfold tailWord_1441895
  simp only [CollatzResearch.WordTrace]
  refine ⟨52590231111268145905663139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35060154074178763937108759 52590231111268145905663139)
  ·
    refine ⟨78885346666902218858494709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52590231111268145905663139 78885346666902218858494709)
    ·
      refine ⟨7395501250022083017983879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78885346666902218858494709 7395501250022083017983879)
      ·
        refine ⟨11093251875033124526975819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395501250022083017983879 11093251875033124526975819)
        ·
          refine ⟨16639877812549686790463729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11093251875033124526975819 16639877812549686790463729)
          ·
            refine ⟨12479908359412265092847797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16639877812549686790463729 12479908359412265092847797)
            ·
              refine ⟨1169991408694899852454481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12479908359412265092847797 1169991408694899852454481)
              ·
                refine ⟨877493556521174889340861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169991408694899852454481 877493556521174889340861)
                ·
                  refine ⟨329060083695440583502823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877493556521174889340861 329060083695440583502823)
                  ·
                    rfl

theorem cell21_1441895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 3].length) (baseStart_1441895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441895 prefixEnd_1441895 := by exact prefixLift 1441895
  have htrace : WordTrace (prefixWord ++ tailWord_1441895) baseStart_1441895 baseEnd_1441895 := by
    simpa [prefixWord, tailWord_1441895, baseEnd_1441895] using wordTrace_append hprefix tailTrace_1441895
  have hstable : (prefixWord ++ tailWord_1441895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441895).length < 2 ^ (prefixWord ++ tailWord_1441895).sum := by decide
  have hdescent : baseEnd_1441895 < baseStart_1441895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441906 : List Nat := [3, 2, 1, 2, 2, 2, 1, 8]
def baseStart_1441906 : Nat := 118140960795 + 1441906 * 2 ^ 59
def prefixEnd_1441906 : Nat := 4983230072969 + 3 ^ 40 * 1441906 * 2
def baseEnd_1441906 : Nat := 109687531348435669606489

theorem tailTrace_1441906 : CollatzResearch.WordTrace tailWord_1441906 prefixEnd_1441906 109687531348435669606489 := by
  unfold tailWord_1441906
  simp only [CollatzResearch.WordTrace]
  refine ⟨13147658078557073696078393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35060421542818863189542381 13147658078557073696078393)
  ·
    refine ⟨9860743558917805272058795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13147658078557073696078393 9860743558917805272058795)
    ·
      refine ⟨14791115338376707908088193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9860743558917805272058795 14791115338376707908088193)
      ·
        refine ⟨11093336503782530931066145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14791115338376707908088193 11093336503782530931066145)
        ·
          refine ⟨8320002377836898198299609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11093336503782530931066145 8320002377836898198299609)
          ·
            refine ⟨6240001783377673648724707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8320002377836898198299609 6240001783377673648724707)
            ·
              refine ⟨9360002675066510473087061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6240001783377673648724707 9360002675066510473087061)
              ·
                refine ⟨109687531348435669606489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9360002675066510473087061 109687531348435669606489)
                ·
                  rfl

theorem cell21_1441906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_1441906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441906 prefixEnd_1441906 := by exact prefixLift 1441906
  have htrace : WordTrace (prefixWord ++ tailWord_1441906) baseStart_1441906 baseEnd_1441906 := by
    simpa [prefixWord, tailWord_1441906, baseEnd_1441906] using wordTrace_append hprefix tailTrace_1441906
  have hstable : (prefixWord ++ tailWord_1441906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441906).length < 2 ^ (prefixWord ++ tailWord_1441906).sum := by decide
  have hdescent : baseEnd_1441906 < baseStart_1441906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441920 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_1441920 : Nat := 118140960795 + 1441920 * 2 ^ 59
def prefixEnd_1441920 : Nat := 4983230072969 + 3 ^ 40 * 1441920 * 2
def baseEnd_1441920 : Nat := 329065789036046095586105

theorem tailTrace_1441920 : CollatzResearch.WordTrace tailWord_1441920 prefixEnd_1441920 329065789036046095586105 := by
  unfold tailWord_1441920
  simp only [CollatzResearch.WordTrace]
  refine ⟨26295571468088787587661607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35060761957451716783548809 26295571468088787587661607)
  ·
    refine ⟨39443357202133181381492411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26295571468088787587661607 39443357202133181381492411)
    ·
      refine ⟨59165035803199772072238617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39443357202133181381492411 59165035803199772072238617)
      ·
        refine ⟨44373776852399829054178963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59165035803199772072238617 44373776852399829054178963)
        ·
          refine ⟨66560665278599743581268445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44373776852399829054178963 66560665278599743581268445)
          ·
            refine ⟨24960249479474903842975667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66560665278599743581268445 24960249479474903842975667)
            ·
              refine ⟨37440374219212355764463501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24960249479474903842975667 37440374219212355764463501)
              ·
                refine ⟨14040140332204633411673813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37440374219212355764463501 14040140332204633411673813)
                ·
                  refine ⟨329065789036046095586105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14040140332204633411673813 329065789036046095586105)
                  ·
                    rfl

theorem cell21_1441920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_1441920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441920 prefixEnd_1441920 := by exact prefixLift 1441920
  have htrace : WordTrace (prefixWord ++ tailWord_1441920) baseStart_1441920 baseEnd_1441920 := by
    simpa [prefixWord, tailWord_1441920, baseEnd_1441920] using wordTrace_append hprefix tailTrace_1441920
  have hstable : (prefixWord ++ tailWord_1441920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441920).length < 2 ^ (prefixWord ++ tailWord_1441920).sum := by decide
  have hdescent : baseEnd_1441920 < baseStart_1441920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441940 : List Nat := [2, 4, 2, 3, 2, 8]
def baseStart_1441940 : Nat := 118140960795 + 1441940 * 2 ^ 59
def prefixEnd_1441940 : Nat := 4983230072969 + 3 ^ 40 * 1441940 * 2
def baseEnd_1441940 : Nat := 12187790863278907601953

theorem tailTrace_1441940 : CollatzResearch.WordTrace tailWord_1441940 prefixEnd_1441940 12187790863278907601953 := by
  unfold tailWord_1441940
  simp only [CollatzResearch.WordTrace]
  refine ⟨26295936198052559295525637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35061248264070079060700849 26295936198052559295525637)
  ·
    refine ⟨4930488037134854867911057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26295936198052559295525637 4930488037134854867911057)
    ·
      refine ⟨3697866027851141150933293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4930488037134854867911057 3697866027851141150933293)
      ·
        refine ⟨1386699760444177931599985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3697866027851141150933293 1386699760444177931599985)
        ·
          refine ⟨1040024820333133448699989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1386699760444177931599985 1040024820333133448699989)
          ·
            refine ⟨12187790863278907601953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1040024820333133448699989 12187790863278907601953)
            ·
              rfl

theorem cell21_1441940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 8].length) (baseStart_1441940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1441940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1441940 prefixEnd_1441940 := by exact prefixLift 1441940
  have htrace : WordTrace (prefixWord ++ tailWord_1441940) baseStart_1441940 baseEnd_1441940 := by
    simpa [prefixWord, tailWord_1441940, baseEnd_1441940] using wordTrace_append hprefix tailTrace_1441940
  have hstable : (prefixWord ++ tailWord_1441940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441940).length < 2 ^ (prefixWord ++ tailWord_1441940).sum := by decide
  have hdescent : baseEnd_1441940 < baseStart_1441940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442078 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1442078 : Nat := 118140960795 + 1442078 * 2 ^ 59
def prefixEnd_1442078 : Nat := 4983230072969 + 3 ^ 40 * 1442078 * 2
def baseEnd_1442078 : Nat := 329101846788672931952449

theorem tailTrace_1442078 : CollatzResearch.WordTrace tailWord_1442078 prefixEnd_1442078 329101846788672931952449 := by
  unfold tailWord_1442078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574613208700646019946861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35064603779736778773049925 6574613208700646019946861)
  ·
    refine ⟨2465479953262742257480073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6574613208700646019946861 2465479953262742257480073)
    ·
      refine ⟨1849109964947056693110055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2465479953262742257480073 1849109964947056693110055)
      ·
        refine ⟨2773664947420585039665083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849109964947056693110055 2773664947420585039665083)
        ·
          refine ⟨4160497421130877559497625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773664947420585039665083 4160497421130877559497625)
          ·
            refine ⟨3120373065848158169623219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4160497421130877559497625 3120373065848158169623219)
            ·
              refine ⟨4680559598772237254434829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120373065848158169623219 4680559598772237254434829)
              ·
                refine ⟨1755209849539588970413061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4680559598772237254434829 1755209849539588970413061)
                ·
                  refine ⟨329101846788672931952449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1755209849539588970413061 329101846788672931952449)
                  ·
                    rfl

theorem cell21_1442078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1442078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442078 prefixEnd_1442078 := by exact prefixLift 1442078
  have htrace : WordTrace (prefixWord ++ tailWord_1442078) baseStart_1442078 baseEnd_1442078 := by
    simpa [prefixWord, tailWord_1442078, baseEnd_1442078] using wordTrace_append hprefix tailTrace_1442078
  have hstable : (prefixWord ++ tailWord_1442078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442078).length < 2 ^ (prefixWord ++ tailWord_1442078).sum := by decide
  have hdescent : baseEnd_1442078 < baseStart_1442078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442151 : List Nat := [1, 1, 5, 1, 3, 2, 3, 5]
def baseStart_1442151 : Nat := 118140960795 + 1442151 * 2 ^ 59
def prefixEnd_1442151 : Nat := 4983230072969 + 3 ^ 40 * 1442151 * 2
def baseEnd_1442151 : Nat := 109706168794413675745211

theorem tailTrace_1442151 : CollatzResearch.WordTrace tailWord_1442151 prefixEnd_1442151 109706168794413675745211 := by
  unfold tailWord_1442151
  simp only [CollatzResearch.WordTrace]
  refine ⟨52599568198340701626982307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35066378798893801084654871 52599568198340701626982307)
  ·
    refine ⟨78899352297511052440473461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52599568198340701626982307 78899352297511052440473461)
    ·
      refine ⟨7396814277891661166294387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78899352297511052440473461 7396814277891661166294387)
      ·
        refine ⟨11095221416837491749441581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7396814277891661166294387 11095221416837491749441581)
        ·
          refine ⟨4160708031314059406040593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11095221416837491749441581 4160708031314059406040593)
          ·
            refine ⟨3120531023485544554530445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4160708031314059406040593 3120531023485544554530445)
            ·
              refine ⟨1170199133807079207948917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3120531023485544554530445 1170199133807079207948917)
              ·
                refine ⟨109706168794413675745211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1170199133807079207948917 109706168794413675745211)
                ·
                  rfl

theorem cell21_1442151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 5].length) (baseStart_1442151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442151 prefixEnd_1442151 := by exact prefixLift 1442151
  have htrace : WordTrace (prefixWord ++ tailWord_1442151) baseStart_1442151 baseEnd_1442151 := by
    simpa [prefixWord, tailWord_1442151, baseEnd_1442151] using wordTrace_append hprefix tailTrace_1442151
  have hstable : (prefixWord ++ tailWord_1442151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442151).length < 2 ^ (prefixWord ++ tailWord_1442151).sum := by decide
  have hdescent : baseEnd_1442151 < baseStart_1442151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442210 : List Nat := [3, 3, 1, 2, 1, 1, 3, 7]
def baseStart_1442210 : Nat := 118140960795 + 1442210 * 2 ^ 59
def prefixEnd_1442210 : Nat := 4983230072969 + 3 ^ 40 * 1442210 * 2
def baseEnd_1442210 : Nat := 109710656995690011917393

theorem tailTrace_1442210 : CollatzResearch.WordTrace tailWord_1442210 prefixEnd_1442210 109710656995690011917393 := by
  unfold tailWord_1442210
  simp only [CollatzResearch.WordTrace]
  refine ⟨13150430026281738675845021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35067813403417969802253389 13150430026281738675845021)
  ·
    refine ⟨4931411259855652003441883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13150430026281738675845021 4931411259855652003441883)
    ·
      refine ⟨7397116889783478005162825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4931411259855652003441883 7397116889783478005162825)
      ·
        refine ⟨5547837667337608503872119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7397116889783478005162825 5547837667337608503872119)
        ·
          refine ⟨8321756501006412755808179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5547837667337608503872119 8321756501006412755808179)
          ·
            refine ⟨12482634751509619133712269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8321756501006412755808179 12482634751509619133712269)
            ·
              refine ⟨4680988031816107175142101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12482634751509619133712269 4680988031816107175142101)
              ·
                refine ⟨109710656995690011917393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4680988031816107175142101 109710656995690011917393)
                ·
                  rfl

theorem cell21_1442210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_1442210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442210 prefixEnd_1442210 := by exact prefixLift 1442210
  have htrace : WordTrace (prefixWord ++ tailWord_1442210) baseStart_1442210 baseEnd_1442210 := by
    simpa [prefixWord, tailWord_1442210, baseEnd_1442210] using wordTrace_append hprefix tailTrace_1442210
  have hstable : (prefixWord ++ tailWord_1442210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442210).length < 2 ^ (prefixWord ++ tailWord_1442210).sum := by decide
  have hdescent : baseEnd_1442210 < baseStart_1442210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442216 : List Nat := [2, 1, 6, 1, 1, 3, 1, 3, 3]
def baseStart_1442216 : Nat := 118140960795 + 1442216 * 2 ^ 59
def prefixEnd_1442216 : Nat := 4983230072969 + 3 ^ 40 * 1442216 * 2
def baseEnd_1442216 : Nat := 329133340268815358652167

theorem tailTrace_1442216 : CollatzResearch.WordTrace tailWord_1442216 prefixEnd_1442216 329133340268815358652167 := by
  unfold tailWord_1442216
  simp only [CollatzResearch.WordTrace]
  refine ⟨26300969471552608864049251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35067959295403478485399001 26300969471552608864049251)
  ·
    refine ⟨39451454207328913296073877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26300969471552608864049251 39451454207328913296073877)
    ·
      refine ⟨1849286915968542810753463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39451454207328913296073877 1849286915968542810753463)
      ·
        refine ⟨2773930373952814216130195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849286915968542810753463 2773930373952814216130195)
        ·
          refine ⟨4160895560929221324195293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773930373952814216130195 4160895560929221324195293)
          ·
            refine ⟨1560335835348457996573235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4160895560929221324195293 1560335835348457996573235)
            ·
              refine ⟨2340503753022686994859853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1560335835348457996573235 2340503753022686994859853)
              ·
                refine ⟨877688907383507623072445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2340503753022686994859853 877688907383507623072445)
                ·
                  refine ⟨329133340268815358652167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877688907383507623072445 329133340268815358652167)
                  ·
                    rfl

theorem cell21_1442216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 3].length) (baseStart_1442216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442216 prefixEnd_1442216 := by exact prefixLift 1442216
  have htrace : WordTrace (prefixWord ++ tailWord_1442216) baseStart_1442216 baseEnd_1442216 := by
    simpa [prefixWord, tailWord_1442216, baseEnd_1442216] using wordTrace_append hprefix tailTrace_1442216
  have hstable : (prefixWord ++ tailWord_1442216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442216).length < 2 ^ (prefixWord ++ tailWord_1442216).sum := by decide
  have hdescent : baseEnd_1442216 < baseStart_1442216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442300 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_1442300 : Nat := 118140960795 + 1442300 * 2 ^ 59
def prefixEnd_1442300 : Nat := 4983230072969 + 3 ^ 40 * 1442300 * 2
def baseEnd_1442300 : Nat := 329152510213249879251995

theorem tailTrace_1442300 : CollatzResearch.WordTrace tailWord_1442300 prefixEnd_1442300 329152510213249879251995 := by
  unfold tailWord_1442300
  simp only [CollatzResearch.WordTrace]
  refine ⟨26302501337400450037078177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35070001783200600049437569 26302501337400450037078177)
  ·
    refine ⟨19726876003050337527808633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26302501337400450037078177 19726876003050337527808633)
    ·
      refine ⟨14795157002287753145856475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19726876003050337527808633 14795157002287753145856475)
      ·
        refine ⟨22192735503431629718784713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14795157002287753145856475 22192735503431629718784713)
        ·
          refine ⟨16644551627573722289088535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22192735503431629718784713 16644551627573722289088535)
          ·
            refine ⟨24966827441360583433632803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16644551627573722289088535 24966827441360583433632803)
            ·
              refine ⟨37450241162040875150449205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24966827441360583433632803 37450241162040875150449205)
              ·
                refine ⟨3510960108941332045354613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37450241162040875150449205 3510960108941332045354613)
                ·
                  refine ⟨329152510213249879251995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3510960108941332045354613 329152510213249879251995)
                  ·
                    rfl

theorem cell21_1442300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_1442300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442300 prefixEnd_1442300 := by exact prefixLift 1442300
  have htrace : WordTrace (prefixWord ++ tailWord_1442300) baseStart_1442300 baseEnd_1442300 := by
    simpa [prefixWord, tailWord_1442300, baseEnd_1442300] using wordTrace_append hprefix tailTrace_1442300
  have hstable : (prefixWord ++ tailWord_1442300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442300).length < 2 ^ (prefixWord ++ tailWord_1442300).sum := by decide
  have hdescent : baseEnd_1442300 < baseStart_1442300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442365 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 4]
def baseStart_1442365 : Nat := 118140960795 + 1442365 * 2 ^ 59
def prefixEnd_1442365 : Nat := 4983230072969 + 3 ^ 40 * 1442365 * 2
def baseEnd_1442365 : Nat := 329167344098824210668529

theorem tailTrace_1442365 : CollatzResearch.WordTrace tailWord_1442365 prefixEnd_1442365 329167344098824210668529 := by
  unfold tailWord_1442365
  simp only [CollatzResearch.WordTrace]
  refine ⟨52607373419565416175272549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35071582279710277450181699 52607373419565416175272549)
  ·
    refine ⟨9863882516168515532863603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52607373419565416175272549 9863882516168515532863603)
    ·
      refine ⟨14795823774252773299295405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9863882516168515532863603 14795823774252773299295405)
      ·
        refine ⟨5548433915344789987235777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14795823774252773299295405 5548433915344789987235777)
        ·
          refine ⟨4161325436508592490426833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5548433915344789987235777 4161325436508592490426833)
          ·
            refine ⟨3120994077381444367820125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4161325436508592490426833 3120994077381444367820125)
            ·
              refine ⟨1170372779018041637932547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3120994077381444367820125 1170372779018041637932547)
              ·
                refine ⟨1755559168527062456898821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170372779018041637932547 1755559168527062456898821)
                ·
                  refine ⟨329167344098824210668529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1755559168527062456898821 329167344098824210668529)
                  ·
                    rfl

theorem cell21_1442365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_1442365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442365 prefixEnd_1442365 := by exact prefixLift 1442365
  have htrace : WordTrace (prefixWord ++ tailWord_1442365) baseStart_1442365 baseEnd_1442365 := by
    simpa [prefixWord, tailWord_1442365, baseEnd_1442365] using wordTrace_append hprefix tailTrace_1442365
  have hstable : (prefixWord ++ tailWord_1442365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442365).length < 2 ^ (prefixWord ++ tailWord_1442365).sum := by decide
  have hdescent : baseEnd_1442365 < baseStart_1442365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442407 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 4]
def baseStart_1442407 : Nat := 118140960795 + 1442407 * 2 ^ 59
def prefixEnd_1442407 : Nat := 4983230072969 + 3 ^ 40 * 1442407 * 2
def baseEnd_1442407 : Nat := 329176929071041470968443

theorem tailTrace_1442407 : CollatzResearch.WordTrace tailWord_1442407 prefixEnd_1442407 329176929071041470968443 := by
  unfold tailWord_1442407
  simp only [CollatzResearch.WordTrace]
  refine ⟨52608905285413257348301475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35072603523608838232200983 52608905285413257348301475)
  ·
    refine ⟨78913357928119886022452213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52608905285413257348301475 78913357928119886022452213)
    ·
      refine ⟨7398127305761239314604895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78913357928119886022452213 7398127305761239314604895)
      ·
        refine ⟨11097190958641858971907343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7398127305761239314604895 11097190958641858971907343)
        ·
          refine ⟨16645786437962788457861015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11097190958641858971907343 16645786437962788457861015)
          ·
            refine ⟨24968679656944182686791523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16645786437962788457861015 24968679656944182686791523)
            ·
              refine ⟨37453019485416274030187285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24968679656944182686791523 37453019485416274030187285)
              ·
                refine ⟨1755610288378887845165029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37453019485416274030187285 1755610288378887845165029)
                ·
                  refine ⟨329176929071041470968443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1755610288378887845165029 329176929071041470968443)
                  ·
                    rfl

theorem cell21_1442407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 4].length) (baseStart_1442407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442407 prefixEnd_1442407 := by exact prefixLift 1442407
  have htrace : WordTrace (prefixWord ++ tailWord_1442407) baseStart_1442407 baseEnd_1442407 := by
    simpa [prefixWord, tailWord_1442407, baseEnd_1442407] using wordTrace_append hprefix tailTrace_1442407
  have hstable : (prefixWord ++ tailWord_1442407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442407).length < 2 ^ (prefixWord ++ tailWord_1442407).sum := by decide
  have hdescent : baseEnd_1442407 < baseStart_1442407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442483 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 4]
def baseStart_1442483 : Nat := 118140960795 + 1442483 * 2 ^ 59
def prefixEnd_1442483 : Nat := 4983230072969 + 3 ^ 40 * 1442483 * 2
def baseEnd_1442483 : Nat := 329194273306482227701621

theorem tailTrace_1442483 : CollatzResearch.WordTrace tailWord_1442483 prefixEnd_1442483 329194273306482227701621 := by
  unfold tailWord_1442483
  simp only [CollatzResearch.WordTrace]
  refine ⟨52611677233137922328068103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35074451488758614885378735 52611677233137922328068103)
  ·
    refine ⟨78917515849706883492102155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52611677233137922328068103 78917515849706883492102155)
    ·
      refine ⟨118376273774560325238153233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78917515849706883492102155 118376273774560325238153233)
      ·
        refine ⟨88782205330920243928614925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118376273774560325238153233 88782205330920243928614925)
        ·
          refine ⟨33293326999095091473230597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88782205330920243928614925 33293326999095091473230597)
          ·
            refine ⟨6242498812330329651230737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33293326999095091473230597 6242498812330329651230737)
            ·
              refine ⟨4681874109247747238423053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6242498812330329651230737 4681874109247747238423053)
              ·
                refine ⟨1755702790967905214408645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4681874109247747238423053 1755702790967905214408645)
                ·
                  refine ⟨329194273306482227701621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1755702790967905214408645 329194273306482227701621)
                  ·
                    rfl

theorem cell21_1442483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 4].length) (baseStart_1442483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442483 prefixEnd_1442483 := by exact prefixLift 1442483
  have htrace : WordTrace (prefixWord ++ tailWord_1442483) baseStart_1442483 baseEnd_1442483 := by
    simpa [prefixWord, tailWord_1442483, baseEnd_1442483] using wordTrace_append hprefix tailTrace_1442483
  have hstable : (prefixWord ++ tailWord_1442483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442483).length < 2 ^ (prefixWord ++ tailWord_1442483).sum := by decide
  have hdescent : baseEnd_1442483 < baseStart_1442483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442514 : List Nat := [3, 2, 2, 2, 3, 1, 8]
def baseStart_1442514 : Nat := 118140960795 + 1442514 * 2 ^ 59
def prefixEnd_1442514 : Nat := 4983230072969 + 3 ^ 40 * 1442514 * 2
def baseEnd_1442514 : Nat := 36577927547648118076099

theorem tailTrace_1442514 : CollatzResearch.WordTrace tailWord_1442514 prefixEnd_1442514 36577927547648118076099 := by
  unfold tailWord_1442514
  simp only [CollatzResearch.WordTrace]
  refine ⟨13153201974006403655611649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35075205264017076414964397 13153201974006403655611649)
  ·
    refine ⟨9864901480504802741708737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13153201974006403655611649 9864901480504802741708737)
    ·
      refine ⟨7398676110378602056281553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9864901480504802741708737 7398676110378602056281553)
      ·
        refine ⟨5549007082783951542211165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7398676110378602056281553 5549007082783951542211165)
        ·
          refine ⟨2080877656043981828329187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5549007082783951542211165 2080877656043981828329187)
          ·
            refine ⟨3121316484065972742493781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080877656043981828329187 3121316484065972742493781)
            ·
              refine ⟨36577927547648118076099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3121316484065972742493781 36577927547648118076099)
              ·
                rfl

theorem cell21_1442514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 8].length) (baseStart_1442514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442514 prefixEnd_1442514 := by exact prefixLift 1442514
  have htrace : WordTrace (prefixWord ++ tailWord_1442514) baseStart_1442514 baseEnd_1442514 := by
    simpa [prefixWord, tailWord_1442514, baseEnd_1442514] using wordTrace_append hprefix tailTrace_1442514
  have hstable : (prefixWord ++ tailWord_1442514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442514).length < 2 ^ (prefixWord ++ tailWord_1442514).sum := by decide
  have hdescent : baseEnd_1442514 < baseStart_1442514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442548 : List Nat := [2, 6, 1, 1, 2, 1, 1, 7]
def baseStart_1442548 : Nat := 118140960795 + 1442548 * 2 ^ 59
def prefixEnd_1442548 : Nat := 4983230072969 + 3 ^ 40 * 1442548 * 2
def baseEnd_1442548 : Nat := 109736369064018853039385

theorem tailTrace_1442548 : CollatzResearch.WordTrace tailWord_1442548 prefixEnd_1442548 109736369064018853039385 := by
  unfold tailWord_1442548
  simp only [CollatzResearch.WordTrace]
  refine ⟨26307023988951219214592149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35076031985268292286122865 26307023988951219214592149)
  ·
    refine ⟨1233141749482088400684007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26307023988951219214592149 1233141749482088400684007)
    ·
      refine ⟨1849712624223132601026011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1233141749482088400684007 1849712624223132601026011)
      ·
        refine ⟨2774568936334698901539017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849712624223132601026011 2774568936334698901539017)
        ·
          refine ⟨2080926702251024176154263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2774568936334698901539017 2080926702251024176154263)
          ·
            refine ⟨3121390053376536264231395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080926702251024176154263 3121390053376536264231395)
            ·
              refine ⟨4682085080064804396347093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3121390053376536264231395 4682085080064804396347093)
              ·
                refine ⟨109736369064018853039385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4682085080064804396347093 109736369064018853039385)
                ·
                  rfl

theorem cell21_1442548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_1442548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442548 prefixEnd_1442548 := by exact prefixLift 1442548
  have htrace : WordTrace (prefixWord ++ tailWord_1442548) baseStart_1442548 baseEnd_1442548 := by
    simpa [prefixWord, tailWord_1442548, baseEnd_1442548] using wordTrace_append hprefix tailTrace_1442548
  have hstable : (prefixWord ++ tailWord_1442548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442548).length < 2 ^ (prefixWord ++ tailWord_1442548).sum := by decide
  have hdescent : baseEnd_1442548 < baseStart_1442548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442630 : List Nat := [6, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1442630 : Nat := 118140960795 + 1442630 * 2 ^ 59
def prefixEnd_1442630 : Nat := 4983230072969 + 3 ^ 40 * 1442630 * 2
def baseEnd_1442630 : Nat := 329227820709242638751321

theorem tailTrace_1442630 : CollatzResearch.WordTrace tailWord_1442630 prefixEnd_1442630 329227820709242638751321 := by
  unfold tailWord_1442630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644282461362667701052167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35078025842403577622446229 1644282461362667701052167)
  ·
    refine ⟨2466423692044001551578251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1644282461362667701052167 2466423692044001551578251)
    ·
      refine ⟨3699635538066002327367377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2466423692044001551578251 3699635538066002327367377)
      ·
        refine ⟨2774726653549501745525533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3699635538066002327367377 2774726653549501745525533)
        ·
          refine ⟨1040522495081063154572075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2774726653549501745525533 1040522495081063154572075)
          ·
            refine ⟨1560783742621594731858113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040522495081063154572075 1560783742621594731858113)
            ·
              refine ⟨1170587806966196048893585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1560783742621594731858113 1170587806966196048893585)
              ·
                refine ⟨877940855224647036670189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170587806966196048893585 877940855224647036670189)
                ·
                  refine ⟨329227820709242638751321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877940855224647036670189 329227820709242638751321)
                  ·
                    rfl

theorem cell21_1442630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1442630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442630 prefixEnd_1442630 := by exact prefixLift 1442630
  have htrace : WordTrace (prefixWord ++ tailWord_1442630) baseStart_1442630 baseEnd_1442630 := by
    simpa [prefixWord, tailWord_1442630, baseEnd_1442630] using wordTrace_append hprefix tailTrace_1442630
  have hstable : (prefixWord ++ tailWord_1442630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442630).length < 2 ^ (prefixWord ++ tailWord_1442630).sum := by decide
  have hdescent : baseEnd_1442630 < baseStart_1442630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442649 : List Nat := [1, 2, 1, 2, 2, 4, 3, 6]
def baseStart_1442649 : Nat := 118140960795 + 1442649 * 2 ^ 59
def prefixEnd_1442649 : Nat := 4983230072969 + 3 ^ 40 * 1442649 * 2
def baseEnd_1442649 : Nat := 109744052256034275978205

theorem tailTrace_1442649 : CollatzResearch.WordTrace tailWord_1442649 prefixEnd_1442649 109744052256034275978205 := by
  unfold tailWord_1442649
  simp only [CollatzResearch.WordTrace]
  refine ⟨52617731750536532678611001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35078487833691021785740667 52617731750536532678611001)
  ·
    refine ⟨39463298812902399508958251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52617731750536532678611001 39463298812902399508958251)
    ·
      refine ⟨59194948219353599263437377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39463298812902399508958251 59194948219353599263437377)
      ·
        refine ⟨44396211164515199447578033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59194948219353599263437377 44396211164515199447578033)
        ·
          refine ⟨33297158373386399585683525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44396211164515199447578033 33297158373386399585683525)
          ·
            refine ⟨6243217195009949922315661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33297158373386399585683525 6243217195009949922315661)
            ·
              refine ⟨2341206448128731220868373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6243217195009949922315661 2341206448128731220868373)
              ·
                refine ⟨109744052256034275978205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2341206448128731220868373 109744052256034275978205)
                ·
                  rfl

theorem cell21_1442649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 6].length) (baseStart_1442649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442649 prefixEnd_1442649 := by exact prefixLift 1442649
  have htrace : WordTrace (prefixWord ++ tailWord_1442649) baseStart_1442649 baseEnd_1442649 := by
    simpa [prefixWord, tailWord_1442649, baseEnd_1442649] using wordTrace_append hprefix tailTrace_1442649
  have hstable : (prefixWord ++ tailWord_1442649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442649).length < 2 ^ (prefixWord ++ tailWord_1442649).sum := by decide
  have hdescent : baseEnd_1442649 < baseStart_1442649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442652 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 4]
def baseStart_1442652 : Nat := 118140960795 + 1442652 * 2 ^ 59
def prefixEnd_1442652 : Nat := 4983230072969 + 3 ^ 40 * 1442652 * 2
def baseEnd_1442652 : Nat := 329232841408975489384609

theorem tailTrace_1442652 : CollatzResearch.WordTrace tailWord_1442652 prefixEnd_1442652 329232841408975489384609 := by
  unfold tailWord_1442652
  simp only [CollatzResearch.WordTrace]
  refine ⟨26308920584762832095485105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35078560779683776127313473 26308920584762832095485105)
  ·
    refine ⟨19731690438572124071613829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26308920584762832095485105 19731690438572124071613829)
    ·
      refine ⟨3699691957232273263427593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19731690438572124071613829 3699691957232273263427593)
      ·
        refine ⟨2774768967924204947570695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3699691957232273263427593 2774768967924204947570695)
        ·
          refine ⟨4162153451886307421356043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774768967924204947570695 4162153451886307421356043)
          ·
            refine ⟨6243230177829461132034065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162153451886307421356043 6243230177829461132034065)
            ·
              refine ⟨4682422633372095849025549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6243230177829461132034065 4682422633372095849025549)
              ·
                refine ⟨1755908487514535943384581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4682422633372095849025549 1755908487514535943384581)
                ·
                  refine ⟨329232841408975489384609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1755908487514535943384581 329232841408975489384609)
                  ·
                    rfl

theorem cell21_1442652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_1442652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442652 prefixEnd_1442652 := by exact prefixLift 1442652
  have htrace : WordTrace (prefixWord ++ tailWord_1442652) baseStart_1442652 baseEnd_1442652 := by
    simpa [prefixWord, tailWord_1442652, baseEnd_1442652] using wordTrace_append hprefix tailTrace_1442652
  have hstable : (prefixWord ++ tailWord_1442652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442652).length < 2 ^ (prefixWord ++ tailWord_1442652).sum := by decide
  have hdescent : baseEnd_1442652 < baseStart_1442652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442686 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_1442686 : Nat := 118140960795 + 1442686 * 2 ^ 59
def prefixEnd_1442686 : Nat := 4983230072969 + 3 ^ 40 * 1442686 * 2
def baseEnd_1442686 : Nat := 329240600672198985817873

theorem tailTrace_1442686 : CollatzResearch.WordTrace tailWord_1442686 prefixEnd_1442686 329240600672198985817873 := by
  unfold tailWord_1442686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6577385156425310999713489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35079387500934991998471941 6577385156425310999713489)
  ·
    refine ⟨4933038867318983249785117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6577385156425310999713489 4933038867318983249785117)
    ·
      refine ⟨1849889575244618718669419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4933038867318983249785117 1849889575244618718669419)
      ·
        refine ⟨2774834362866928078004129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849889575244618718669419 2774834362866928078004129)
        ·
          refine ⟨2081125772150196058503097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2774834362866928078004129 2081125772150196058503097)
          ·
            refine ⟨1560844329112647043877323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2081125772150196058503097 1560844329112647043877323)
            ·
              refine ⟨2341266493668970565815985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1560844329112647043877323 2341266493668970565815985)
              ·
                refine ⟨1755949870251727924361989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2341266493668970565815985 1755949870251727924361989)
                ·
                  refine ⟨329240600672198985817873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1755949870251727924361989 329240600672198985817873)
                  ·
                    rfl

theorem cell21_1442686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_1442686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442686 prefixEnd_1442686 := by exact prefixLift 1442686
  have htrace : WordTrace (prefixWord ++ tailWord_1442686) baseStart_1442686 baseEnd_1442686 := by
    simpa [prefixWord, tailWord_1442686, baseEnd_1442686] using wordTrace_append hprefix tailTrace_1442686
  have hstable : (prefixWord ++ tailWord_1442686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442686).length < 2 ^ (prefixWord ++ tailWord_1442686).sum := by decide
  have hdescent : baseEnd_1442686 < baseStart_1442686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442697 : List Nat := [1, 2, 1, 1, 5, 2, 2, 4, 3]
def baseStart_1442697 : Nat := 118140960795 + 1442697 * 2 ^ 59
def prefixEnd_1442697 : Nat := 4983230072969 + 3 ^ 40 * 1442697 * 2
def baseEnd_1442697 : Nat := 329243111022065411134517

theorem tailTrace_1442697 : CollatzResearch.WordTrace tailWord_1442697 prefixEnd_1442697 329243111022065411134517 := by
  unfold tailWord_1442697
  simp only [CollatzResearch.WordTrace]
  refine ⟨52619482454362636876358345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35079654969575091250905563 52619482454362636876358345)
  ·
    refine ⟨39464611840771977657268759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52619482454362636876358345 39464611840771977657268759)
    ·
      refine ⟨59196917761157966485903139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39464611840771977657268759 59196917761157966485903139)
      ·
        refine ⟨88795376641736949728854709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59196917761157966485903139 88795376641736949728854709)
        ·
          refine ⟨8324566560162839037080129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88795376641736949728854709 8324566560162839037080129)
          ·
            refine ⟨6243424920122129277810097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8324566560162839037080129 6243424920122129277810097)
            ·
              refine ⟨4682568690091596958357573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6243424920122129277810097 4682568690091596958357573)
              ·
                refine ⟨877981629392174429692045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4682568690091596958357573 877981629392174429692045)
                ·
                  refine ⟨329243111022065411134517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877981629392174429692045 329243111022065411134517)
                  ·
                    rfl

theorem cell21_1442697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 3].length) (baseStart_1442697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442697 prefixEnd_1442697 := by exact prefixLift 1442697
  have htrace : WordTrace (prefixWord ++ tailWord_1442697) baseStart_1442697 baseEnd_1442697 := by
    simpa [prefixWord, tailWord_1442697, baseEnd_1442697] using wordTrace_append hprefix tailTrace_1442697
  have hstable : (prefixWord ++ tailWord_1442697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442697).length < 2 ^ (prefixWord ++ tailWord_1442697).sum := by decide
  have hdescent : baseEnd_1442697 < baseStart_1442697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442849 : List Nat := [1, 2, 3, 2, 3, 1, 1, 5, 3]
def baseStart_1442849 : Nat := 118140960795 + 1442849 * 2 ^ 59
def prefixEnd_1442849 : Nat := 4983230072969 + 3 ^ 40 * 1442849 * 2
def baseEnd_1442849 : Nat := 329277799492946924600873

theorem tailTrace_1442849 : CollatzResearch.WordTrace tailWord_1442849 prefixEnd_1442849 329277799492946924600873 := by
  unfold tailWord_1442849
  simp only [CollatzResearch.WordTrace]
  refine ⟨52625026349811966835891601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35083350899874644557261067 52625026349811966835891601)
  ·
    refine ⟨39468769762358975126918701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52625026349811966835891601 39468769762358975126918701)
    ·
      refine ⟨14800788660884615672594513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39468769762358975126918701 14800788660884615672594513)
      ·
        refine ⟨11100591495663461754445885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14800788660884615672594513 11100591495663461754445885)
        ·
          refine ⟨4162721810873798157917207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11100591495663461754445885 4162721810873798157917207)
          ·
            refine ⟨6244082716310697236875811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162721810873798157917207 6244082716310697236875811)
            ·
              refine ⟨9366124074466045855313717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6244082716310697236875811 9366124074466045855313717)
              ·
                refine ⟨878074131981191798935661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9366124074466045855313717 878074131981191798935661)
                ·
                  refine ⟨329277799492946924600873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878074131981191798935661 329277799492946924600873)
                  ·
                    rfl

theorem cell21_1442849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 3].length) (baseStart_1442849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442849 prefixEnd_1442849 := by exact prefixLift 1442849
  have htrace : WordTrace (prefixWord ++ tailWord_1442849) baseStart_1442849 baseEnd_1442849 := by
    simpa [prefixWord, tailWord_1442849, baseEnd_1442849] using wordTrace_append hprefix tailTrace_1442849
  have hstable : (prefixWord ++ tailWord_1442849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442849).length < 2 ^ (prefixWord ++ tailWord_1442849).sum := by decide
  have hdescent : baseEnd_1442849 < baseStart_1442849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442860 : List Nat := [2, 2, 1, 1, 1, 2, 12]
def baseStart_1442860 : Nat := 118140960795 + 1442860 * 2 ^ 59
def prefixEnd_1442860 : Nat := 4983230072969 + 3 ^ 40 * 1442860 * 2
def baseEnd_1442860 : Nat := 36586701093645927768613

theorem tailTrace_1442860 : CollatzResearch.WordTrace tailWord_1442860 prefixEnd_1442860 36586701093645927768613 := by
  unfold tailWord_1442860
  simp only [CollatzResearch.WordTrace]
  refine ⟨26312713776386057857271017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35083618368514743809694689 26312713776386057857271017)
  ·
    refine ⟨19734535332289543392953263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26312713776386057857271017 19734535332289543392953263)
    ·
      refine ⟨29601802998434315089429895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19734535332289543392953263 29601802998434315089429895)
      ·
        refine ⟨44402704497651472634144843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29601802998434315089429895 44402704497651472634144843)
        ·
          refine ⟨66604056746477208951217265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44402704497651472634144843 66604056746477208951217265)
          ·
            refine ⟨49953042559857906713412949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66604056746477208951217265 49953042559857906713412949)
            ·
              refine ⟨36586701093645927768613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 49953042559857906713412949 36586701093645927768613)
              ·
                rfl

theorem cell21_1442860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 12].length) (baseStart_1442860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442860 prefixEnd_1442860 := by exact prefixLift 1442860
  have htrace : WordTrace (prefixWord ++ tailWord_1442860) baseStart_1442860 baseEnd_1442860 := by
    simpa [prefixWord, tailWord_1442860, baseEnd_1442860] using wordTrace_append hprefix tailTrace_1442860
  have hstable : (prefixWord ++ tailWord_1442860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442860).length < 2 ^ (prefixWord ++ tailWord_1442860).sum := by decide
  have hdescent : baseEnd_1442860 < baseStart_1442860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442925 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1442925 : Nat := 118140960795 + 1442925 * 2 ^ 59
def prefixEnd_1442925 : Nat := 4983230072969 + 3 ^ 40 * 1442925 * 2
def baseEnd_1442925 : Nat := 329295143728387681334051

theorem tailTrace_1442925 : CollatzResearch.WordTrace tailWord_1442925 prefixEnd_1442925 329295143728387681334051 := by
  unfold tailWord_1442925
  simp only [CollatzResearch.WordTrace]
  refine ⟨52627798297536631815658229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35085198865024421210438819 52627798297536631815658229)
  ·
    refine ⟨4933856090394059232717959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52627798297536631815658229 4933856090394059232717959)
    ·
      refine ⟨7400784135591088849076939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4933856090394059232717959 7400784135591088849076939)
      ·
        refine ⟨11101176203386633273615409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7400784135591088849076939 11101176203386633273615409)
        ·
          refine ⟨8325882152539974955211557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11101176203386633273615409 8325882152539974955211557)
          ·
            refine ⟨1561102903601245304102167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8325882152539974955211557 1561102903601245304102167)
            ·
              refine ⟨2341654355401867956153251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561102903601245304102167 2341654355401867956153251)
              ·
                refine ⟨3512481533102801934229877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341654355401867956153251 3512481533102801934229877)
                ·
                  refine ⟨329295143728387681334051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3512481533102801934229877 329295143728387681334051)
                  ·
                    rfl

theorem cell21_1442925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1442925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442925 prefixEnd_1442925 := by exact prefixLift 1442925
  have htrace : WordTrace (prefixWord ++ tailWord_1442925) baseStart_1442925 baseEnd_1442925 := by
    simpa [prefixWord, tailWord_1442925, baseEnd_1442925] using wordTrace_append hprefix tailTrace_1442925
  have hstable : (prefixWord ++ tailWord_1442925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442925).length < 2 ^ (prefixWord ++ tailWord_1442925).sum := by decide
  have hdescent : baseEnd_1442925 < baseStart_1442925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442936 : List Nat := [2, 1, 2, 1, 1, 1, 5, 8]
def baseStart_1442936 : Nat := 118140960795 + 1442936 * 2 ^ 59
def prefixEnd_1442936 : Nat := 4983230072969 + 3 ^ 40 * 1442936 * 2
def baseEnd_1442936 : Nat := 109765884692751368883565

theorem tailTrace_1442936 : CollatzResearch.WordTrace tailWord_1442936 prefixEnd_1442936 109765884692751368883565 := by
  unfold tailWord_1442936
  simp only [CollatzResearch.WordTrace]
  refine ⟨26314099750248390347154331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35085466333664520462872441 26314099750248390347154331)
  ·
    refine ⟨39471149625372585520731497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26314099750248390347154331 39471149625372585520731497)
    ·
      refine ⟨29603362219029439140548623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39471149625372585520731497 29603362219029439140548623)
      ·
        refine ⟨44405043328544158710822935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29603362219029439140548623 44405043328544158710822935)
        ·
          refine ⟨66607564992816238066234403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44405043328544158710822935 66607564992816238066234403)
          ·
            refine ⟨99911347489224357099351605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66607564992816238066234403 99911347489224357099351605)
            ·
              refine ⟨9366688827114783478064213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99911347489224357099351605 9366688827114783478064213)
              ·
                refine ⟨109765884692751368883565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9366688827114783478064213 109765884692751368883565)
                ·
                  rfl

theorem cell21_1442936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_1442936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1442936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1442936 prefixEnd_1442936 := by exact prefixLift 1442936
  have htrace : WordTrace (prefixWord ++ tailWord_1442936) baseStart_1442936 baseEnd_1442936 := by
    simpa [prefixWord, tailWord_1442936, baseEnd_1442936] using wordTrace_append hprefix tailTrace_1442936
  have hstable : (prefixWord ++ tailWord_1442936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442936).length < 2 ^ (prefixWord ++ tailWord_1442936).sum := by decide
  have hdescent : baseEnd_1442936 < baseStart_1442936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443029 : List Nat := [1, 3, 2, 4, 1, 2, 8]
def baseStart_1443029 : Nat := 118140960795 + 1443029 * 2 ^ 59
def prefixEnd_1443029 : Nat := 4983230072969 + 3 ^ 40 * 1443029 * 2
def baseEnd_1443029 : Nat := 36590986438367401288945

theorem tailTrace_1443029 : CollatzResearch.WordTrace tailWord_1443029 prefixEnd_1443029 36590986438367401288945 := by
  unfold tailWord_1443029
  simp only [CollatzResearch.WordTrace]
  refine ⟨52631591489159857577444141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35087727659439905051629427 52631591489159857577444141)
  ·
    refine ⟨19736846808434946591541553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52631591489159857577444141 19736846808434946591541553)
    ·
      refine ⟨14802635106326209943656165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19736846808434946591541553 14802635106326209943656165)
      ·
        refine ⟨2775494082436164364435531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14802635106326209943656165 2775494082436164364435531)
        ·
          refine ⟨4163241123654246546653297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2775494082436164364435531 4163241123654246546653297)
          ·
            refine ⟨3122430842740684909989973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4163241123654246546653297 3122430842740684909989973)
            ·
              refine ⟨36590986438367401288945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3122430842740684909989973 36590986438367401288945)
              ·
                rfl

theorem cell21_1443029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 8].length) (baseStart_1443029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443029 prefixEnd_1443029 := by exact prefixLift 1443029
  have htrace : WordTrace (prefixWord ++ tailWord_1443029) baseStart_1443029 baseEnd_1443029 := by
    simpa [prefixWord, tailWord_1443029, baseEnd_1443029] using wordTrace_append hprefix tailTrace_1443029
  have hstable : (prefixWord ++ tailWord_1443029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443029).length < 2 ^ (prefixWord ++ tailWord_1443029).sum := by decide
  have hdescent : baseEnd_1443029 < baseStart_1443029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443032 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 4]
def baseStart_1443032 : Nat := 118140960795 + 1443032 * 2 ^ 59
def prefixEnd_1443032 : Nat := 4983230072969 + 3 ^ 40 * 1443032 * 2
def baseEnd_1443032 : Nat := 329319562586179273050499

theorem tailTrace_1443032 : CollatzResearch.WordTrace tailWord_1443032 prefixEnd_1443032 329319562586179273050499 := by
  unfold tailWord_1443032
  simp only [CollatzResearch.WordTrace]
  refine ⟨26315850454074494544901675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35087800605432659393202233 26315850454074494544901675)
  ·
    refine ⟨39473775681111741817352513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26315850454074494544901675 39473775681111741817352513)
    ·
      refine ⟨29605331760833806363014385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39473775681111741817352513 29605331760833806363014385)
      ·
        refine ⟨22203998820625354772260789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29605331760833806363014385 22203998820625354772260789)
        ·
          refine ⟨2081624889433627009899449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22203998820625354772260789 2081624889433627009899449)
          ·
            refine ⟨1561218667075220257424587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2081624889433627009899449 1561218667075220257424587)
            ·
              refine ⟨2341828000612830386136881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561218667075220257424587 2341828000612830386136881)
              ·
                refine ⟨1756371000459622789602661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2341828000612830386136881 1756371000459622789602661)
                ·
                  refine ⟨329319562586179273050499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1756371000459622789602661 329319562586179273050499)
                  ·
                    rfl

theorem cell21_1443032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_1443032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443032 prefixEnd_1443032 := by exact prefixLift 1443032
  have htrace : WordTrace (prefixWord ++ tailWord_1443032) baseStart_1443032 baseEnd_1443032 := by
    simpa [prefixWord, tailWord_1443032, baseEnd_1443032] using wordTrace_append hprefix tailTrace_1443032
  have hstable : (prefixWord ++ tailWord_1443032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443032).length < 2 ^ (prefixWord ++ tailWord_1443032).sum := by decide
  have hdescent : baseEnd_1443032 < baseStart_1443032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443136 : List Nat := [2, 1, 1, 2, 2, 1, 4, 5, 3]
def baseStart_1443136 : Nat := 118140960795 + 1443136 * 2 ^ 59
def prefixEnd_1443136 : Nat := 4983230072969 + 3 ^ 40 * 1443136 * 2
def baseEnd_1443136 : Nat := 329343296803098203316953

theorem tailTrace_1443136 : CollatzResearch.WordTrace tailWord_1443136 prefixEnd_1443136 329343296803098203316953 := by
  unfold tailWord_1443136
  simp only [CollatzResearch.WordTrace]
  refine ⟨26317747049886107425794631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35090329399848143234392841 26317747049886107425794631)
  ·
    refine ⟨39476620574829161138691947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26317747049886107425794631 39476620574829161138691947)
    ·
      refine ⟨59214930862243741708037921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39476620574829161138691947 59214930862243741708037921)
      ·
        refine ⟨44411198146682806281028441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59214930862243741708037921 44411198146682806281028441)
        ·
          refine ⟨33308398610012104710771331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44411198146682806281028441 33308398610012104710771331)
          ·
            refine ⟨49962597915018157066156997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33308398610012104710771331 49962597915018157066156997)
            ·
              refine ⟨9367987109065904449904437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49962597915018157066156997 9367987109065904449904437)
              ·
                refine ⟨878248791474928542178541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9367987109065904449904437 878248791474928542178541)
                ·
                  refine ⟨329343296803098203316953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878248791474928542178541 329343296803098203316953)
                  ·
                    rfl

theorem cell21_1443136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 3].length) (baseStart_1443136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443136 prefixEnd_1443136 := by exact prefixLift 1443136
  have htrace : WordTrace (prefixWord ++ tailWord_1443136) baseStart_1443136 baseEnd_1443136 := by
    simpa [prefixWord, tailWord_1443136, baseEnd_1443136] using wordTrace_append hprefix tailTrace_1443136
  have hstable : (prefixWord ++ tailWord_1443136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443136).length < 2 ^ (prefixWord ++ tailWord_1443136).sum := by decide
  have hdescent : baseEnd_1443136 < baseStart_1443136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443142 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1443142 : Nat := 118140960795 + 1443142 * 2 ^ 59
def prefixEnd_1443142 : Nat := 4983230072969 + 3 ^ 40 * 1443142 * 2
def baseEnd_1443142 : Nat := 329344666084843526216941

theorem tailTrace_1443142 : CollatzResearch.WordTrace tailWord_1443142 prefixEnd_1443142 329344666084843526216941 := by
  unfold tailWord_1443142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644866029304702433634615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35090475291833651917538453 1644866029304702433634615)
  ·
    refine ⟨2467299043957053650451923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1644866029304702433634615 2467299043957053650451923)
    ·
      refine ⟨3700948565935580475677885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2467299043957053650451923 3700948565935580475677885)
      ·
        refine ⟨1387855712225842678379207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3700948565935580475677885 1387855712225842678379207)
        ·
          refine ⟨2081783568338764017568811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1387855712225842678379207 2081783568338764017568811)
          ·
            refine ⟨3122675352508146026353217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081783568338764017568811 3122675352508146026353217)
            ·
              refine ⟨2342006514381109519764913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3122675352508146026353217 2342006514381109519764913)
              ·
                refine ⟨1756504885785832139823685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2342006514381109519764913 1756504885785832139823685)
                ·
                  refine ⟨329344666084843526216941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1756504885785832139823685 329344666084843526216941)
                  ·
                    rfl

theorem cell21_1443142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1443142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443142 prefixEnd_1443142 := by exact prefixLift 1443142
  have htrace : WordTrace (prefixWord ++ tailWord_1443142) baseStart_1443142 baseEnd_1443142 := by
    simpa [prefixWord, tailWord_1443142, baseEnd_1443142] using wordTrace_append hprefix tailTrace_1443142
  have hstable : (prefixWord ++ tailWord_1443142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443142).length < 2 ^ (prefixWord ++ tailWord_1443142).sum := by decide
  have hdescent : baseEnd_1443142 < baseStart_1443142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443201 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 4]
def baseStart_1443201 : Nat := 118140960795 + 1443201 * 2 ^ 59
def prefixEnd_1443201 : Nat := 4983230072969 + 3 ^ 40 * 1443201 * 2
def baseEnd_1443201 : Nat := 329358130688672534733487

theorem tailTrace_1443201 : CollatzResearch.WordTrace tailWord_1443201 prefixEnd_1443201 329358130688672534733487 := by
  unfold tailWord_1443201
  simp only [CollatzResearch.WordTrace]
  refine ⟨52637864844536730952705457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35091909896357820635136971 52637864844536730952705457)
  ·
    refine ⟨39478398633402548214529093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52637864844536730952705457 39478398633402548214529093)
    ·
      refine ⟨7402199743762977790224205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39478398633402548214529093 7402199743762977790224205)
      ·
        refine ⟨2775824903911116671334077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7402199743762977790224205 2775824903911116671334077)
        ·
          refine ⟨1040934338966668751750279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2775824903911116671334077 1040934338966668751750279)
          ·
            refine ⟨1561401508450003127625419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040934338966668751750279 1561401508450003127625419)
            ·
              refine ⟨2342102262675004691438129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561401508450003127625419 2342102262675004691438129)
              ·
                refine ⟨1756576697006253518578597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2342102262675004691438129 1756576697006253518578597)
                ·
                  refine ⟨329358130688672534733487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1756576697006253518578597 329358130688672534733487)
                  ·
                    rfl

theorem cell21_1443201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 4].length) (baseStart_1443201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443201 prefixEnd_1443201 := by exact prefixLift 1443201
  have htrace : WordTrace (prefixWord ++ tailWord_1443201) baseStart_1443201 baseEnd_1443201 := by
    simpa [prefixWord, tailWord_1443201, baseEnd_1443201] using wordTrace_append hprefix tailTrace_1443201
  have hstable : (prefixWord ++ tailWord_1443201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443201).length < 2 ^ (prefixWord ++ tailWord_1443201).sum := by decide
  have hdescent : baseEnd_1443201 < baseStart_1443201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443212 : List Nat := [2, 2, 1, 2, 1, 3, 1, 6, 3]
def baseStart_1443212 : Nat := 118140960795 + 1443212 * 2 ^ 59
def prefixEnd_1443212 : Nat := 4983230072969 + 3 ^ 40 * 1443212 * 2
def baseEnd_1443212 : Nat := 329360641038538960050131

theorem tailTrace_1443212 : CollatzResearch.WordTrace tailWord_1443212 prefixEnd_1443212 329360641038538960050131 := by
  unfold tailWord_1443212
  simp only [CollatzResearch.WordTrace]
  refine ⟨26319133023748439915677945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35092177364997919887570593 26319133023748439915677945)
  ·
    refine ⟨19739349767811329936758459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26319133023748439915677945 19739349767811329936758459)
    ·
      refine ⟨29609024651716994905137689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19739349767811329936758459 29609024651716994905137689)
      ·
        refine ⟨22206768488787746178853267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29609024651716994905137689 22206768488787746178853267)
        ·
          refine ⟨33310152733181619268279901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22206768488787746178853267 33310152733181619268279901)
          ·
            refine ⟨12491307274943107225604963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33310152733181619268279901 12491307274943107225604963)
            ·
              refine ⟨18736960912414660838407445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12491307274943107225604963 18736960912414660838407445)
              ·
                refine ⟨878295042769437226800349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18736960912414660838407445 878295042769437226800349)
                ·
                  refine ⟨329360641038538960050131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878295042769437226800349 329360641038538960050131)
                  ·
                    rfl

theorem cell21_1443212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_1443212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443212 prefixEnd_1443212 := by exact prefixLift 1443212
  have htrace : WordTrace (prefixWord ++ tailWord_1443212) baseStart_1443212 baseEnd_1443212 := by
    simpa [prefixWord, tailWord_1443212, baseEnd_1443212] using wordTrace_append hprefix tailTrace_1443212
  have hstable : (prefixWord ++ tailWord_1443212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443212).length < 2 ^ (prefixWord ++ tailWord_1443212).sum := by decide
  have hdescent : baseEnd_1443212 < baseStart_1443212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443257 : List Nat := [1, 2, 1, 4, 4, 2, 7]
def baseStart_1443257 : Nat := 118140960795 + 1443257 * 2 ^ 59
def prefixEnd_1443257 : Nat := 4983230072969 + 3 ^ 40 * 1443257 * 2
def baseEnd_1443257 : Nat := 36596767850180986866671

theorem tailTrace_1443257 : CollatzResearch.WordTrace tailWord_1443257 prefixEnd_1443257 36596767850180986866671 := by
  unfold tailWord_1443257
  simp only [CollatzResearch.WordTrace]
  refine ⟨52639907332333852516744025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35093271554889235011162683 52639907332333852516744025)
  ·
    refine ⟨39479930499250389387558019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52639907332333852516744025 39479930499250389387558019)
    ·
      refine ⟨59219895748875584081337029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39479930499250389387558019 59219895748875584081337029)
      ·
        refine ⟨11103730452914172015250693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59219895748875584081337029 11103730452914172015250693)
        ·
          refine ⟨2081949459921407252859505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11103730452914172015250693 2081949459921407252859505)
          ·
            refine ⟨1561462094941055439644629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2081949459921407252859505 1561462094941055439644629)
            ·
              refine ⟨36596767850180986866671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1561462094941055439644629 36596767850180986866671)
              ·
                rfl

theorem cell21_1443257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 7].length) (baseStart_1443257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443257 prefixEnd_1443257 := by exact prefixLift 1443257
  have htrace : WordTrace (prefixWord ++ tailWord_1443257) baseStart_1443257 baseEnd_1443257 := by
    simpa [prefixWord, tailWord_1443257, baseEnd_1443257] using wordTrace_append hprefix tailTrace_1443257
  have hstable : (prefixWord ++ tailWord_1443257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443257).length < 2 ^ (prefixWord ++ tailWord_1443257).sum := by decide
  have hdescent : baseEnd_1443257 < baseStart_1443257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443347 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 5]
def baseStart_1443347 : Nat := 118140960795 + 1443347 * 2 ^ 59
def prefixEnd_1443347 : Nat := 4983230072969 + 3 ^ 40 * 1443347 * 2
def baseEnd_1443347 : Nat := 329391449877808725299855

theorem tailTrace_1443347 : CollatzResearch.WordTrace tailWord_1443347 prefixEnd_1443347 329391449877808725299855 := by
  unfold tailWord_1443347
  simp only [CollatzResearch.WordTrace]
  refine ⟨52643189902007797887520295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35095459934671865258346863 52643189902007797887520295)
  ·
    refine ⟨78964784853011696831280443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52643189902007797887520295 78964784853011696831280443)
    ·
      refine ⟨118447177279517545246920665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78964784853011696831280443 118447177279517545246920665)
      ·
        refine ⟨88835382959638158935190499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118447177279517545246920665 88835382959638158935190499)
        ·
          refine ⟨133253074439457238402785749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88835382959638158935190499 133253074439457238402785749)
          ·
            refine ⟨3123118932174779025065291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 133253074439457238402785749 3123118932174779025065291)
            ·
              refine ⟨4684678398262168537597937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123118932174779025065291 4684678398262168537597937)
              ·
                refine ⟨3513508798696626403198453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4684678398262168537597937 3513508798696626403198453)
                ·
                  refine ⟨329391449877808725299855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3513508798696626403198453 329391449877808725299855)
                  ·
                    rfl

theorem cell21_1443347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 5].length) (baseStart_1443347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443347 prefixEnd_1443347 := by exact prefixLift 1443347
  have htrace : WordTrace (prefixWord ++ tailWord_1443347) baseStart_1443347 baseEnd_1443347 := by
    simpa [prefixWord, tailWord_1443347, baseEnd_1443347] using wordTrace_append hprefix tailTrace_1443347
  have hstable : (prefixWord ++ tailWord_1443347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443347).length < 2 ^ (prefixWord ++ tailWord_1443347).sum := by decide
  have hdescent : baseEnd_1443347 < baseStart_1443347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443440 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 5]
def baseStart_1443440 : Nat := 118140960795 + 1443440 * 2 ^ 59
def prefixEnd_1443440 : Nat := 4983230072969 + 3 ^ 40 * 1443440 * 2
def baseEnd_1443440 : Nat := 329412673744861230249665

theorem tailTrace_1443440 : CollatzResearch.WordTrace tailWord_1443440 prefixEnd_1443440 329412673744861230249665 := by
  unfold tailWord_1443440
  simp only [CollatzResearch.WordTrace]
  refine ⟨26323290945335437385327887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35097721260447249847103849 26323290945335437385327887)
  ·
    refine ⟨39484936418003156077991831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26323290945335437385327887 39484936418003156077991831)
    ·
      refine ⟨59227404627004734116987747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39484936418003156077991831 59227404627004734116987747)
      ·
        refine ⟨88841106940507101175481621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59227404627004734116987747 88841106940507101175481621)
        ·
          refine ⟨4164426887836270367600701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88841106940507101175481621 4164426887836270367600701)
          ·
            refine ⟨1561660082938601387850263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4164426887836270367600701 1561660082938601387850263)
            ·
              refine ⟨2342490124407902081775395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561660082938601387850263 2342490124407902081775395)
              ·
                refine ⟨3513735186611853122663093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342490124407902081775395 3513735186611853122663093)
                ·
                  refine ⟨329412673744861230249665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3513735186611853122663093 329412673744861230249665)
                  ·
                    rfl

theorem cell21_1443440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_1443440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443440 prefixEnd_1443440 := by exact prefixLift 1443440
  have htrace : WordTrace (prefixWord ++ tailWord_1443440) baseStart_1443440 baseEnd_1443440 := by
    simpa [prefixWord, tailWord_1443440, baseEnd_1443440] using wordTrace_append hprefix tailTrace_1443440
  have hstable : (prefixWord ++ tailWord_1443440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443440).length < 2 ^ (prefixWord ++ tailWord_1443440).sum := by decide
  have hdescent : baseEnd_1443440 < baseStart_1443440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443620 : List Nat := [2, 3, 1, 3, 2, 1, 1, 8]
def baseStart_1443620 : Nat := 118140960795 + 1443620 * 2 ^ 59
def prefixEnd_1443620 : Nat := 4983230072969 + 3 ^ 40 * 1443620 * 2
def baseEnd_1443620 : Nat := 109817917399073639083099

theorem tailTrace_1443620 : CollatzResearch.WordTrace tailWord_1443620 prefixEnd_1443620 109817917399073639083099 := by
  unfold tailWord_1443620
  simp only [CollatzResearch.WordTrace]
  refine ⟨26326573515009382756104157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35102098020012510341472209 26326573515009382756104157)
  ·
    refine ⟨9872465068128518533539059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26326573515009382756104157 9872465068128518533539059)
    ·
      refine ⟨14808697602192777800308589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9872465068128518533539059 14808697602192777800308589)
      ·
        refine ⟨5553261600822291675115721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14808697602192777800308589 5553261600822291675115721)
        ·
          refine ⟨4164946200616718756336791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5553261600822291675115721 4164946200616718756336791)
          ·
            refine ⟨6247419300925078134505187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164946200616718756336791 6247419300925078134505187)
            ·
              refine ⟨9371128951387617201757781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6247419300925078134505187 9371128951387617201757781)
              ·
                refine ⟨109817917399073639083099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9371128951387617201757781 109817917399073639083099)
                ·
                  rfl

theorem cell21_1443620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_1443620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443620 prefixEnd_1443620 := by exact prefixLift 1443620
  have htrace : WordTrace (prefixWord ++ tailWord_1443620) baseStart_1443620 baseEnd_1443620 := by
    simpa [prefixWord, tailWord_1443620, baseEnd_1443620] using wordTrace_append hprefix tailTrace_1443620
  have hstable : (prefixWord ++ tailWord_1443620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443620).length < 2 ^ (prefixWord ++ tailWord_1443620).sum := by decide
  have hdescent : baseEnd_1443620 < baseStart_1443620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443702 : List Nat := [5, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_1443702 : Nat := 118140960795 + 1443702 * 2 ^ 59
def prefixEnd_1443702 : Nat := 4983230072969 + 3 ^ 40 * 1443702 * 2
def baseEnd_1443702 : Nat := 329472465714406996882463

theorem tailTrace_1443702 : CollatzResearch.WordTrace tailWord_1443702 prefixEnd_1443702 329472465714406996882463 := by
  unfold tailWord_1443702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3291008613482605844793335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35104091877147795677795573 3291008613482605844793335)
  ·
    refine ⟨4936512920223908767190003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3291008613482605844793335 4936512920223908767190003)
    ·
      refine ⟨7404769380335863150785005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4936512920223908767190003 7404769380335863150785005)
      ·
        refine ⟨2776788517625948681544377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7404769380335863150785005 2776788517625948681544377)
        ·
          refine ⟨2082591388219461511158283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2776788517625948681544377 2082591388219461511158283)
          ·
            refine ⟨3123887082329192266737425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082591388219461511158283 3123887082329192266737425)
            ·
              refine ⟨2342915311746894200053069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3123887082329192266737425 2342915311746894200053069)
              ·
                refine ⟨878593241905085325019901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2342915311746894200053069 878593241905085325019901)
                ·
                  refine ⟨329472465714406996882463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878593241905085325019901 329472465714406996882463)
                  ·
                    rfl

theorem cell21_1443702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_1443702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443702 prefixEnd_1443702 := by exact prefixLift 1443702
  have htrace : WordTrace (prefixWord ++ tailWord_1443702) baseStart_1443702 baseEnd_1443702 := by
    simpa [prefixWord, tailWord_1443702, baseEnd_1443702] using wordTrace_append hprefix tailTrace_1443702
  have hstable : (prefixWord ++ tailWord_1443702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443702).length < 2 ^ (prefixWord ++ tailWord_1443702).sum := by decide
  have hdescent : baseEnd_1443702 < baseStart_1443702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443713 : List Nat := [1, 2, 4, 4, 1, 1, 8]
def baseStart_1443713 : Nat := 118140960795 + 1443713 * 2 ^ 59
def prefixEnd_1443713 : Nat := 4983230072969 + 3 ^ 40 * 1443713 * 2
def baseEnd_1443713 : Nat := 36608330673808158022123

theorem tailTrace_1443713 : CollatzResearch.WordTrace tailWord_1443713 prefixEnd_1443713 36608330673808158022123 := by
  unfold tailWord_1443713
  simp only [CollatzResearch.WordTrace]
  refine ⟨52656539018681842395343793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35104359345787894930229195 52656539018681842395343793)
  ·
    refine ⟨39492404264011381796507845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52656539018681842395343793 39492404264011381796507845)
    ·
      refine ⟨7404825799502134086845221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39492404264011381796507845 7404825799502134086845221)
      ·
        refine ⟨1388404837406650141283479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7404825799502134086845221 1388404837406650141283479)
        ·
          refine ⟨2082607256109975211925219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388404837406650141283479 2082607256109975211925219)
          ·
            refine ⟨3123910884164962817887829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082607256109975211925219 3123910884164962817887829)
            ·
              refine ⟨36608330673808158022123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3123910884164962817887829 36608330673808158022123)
              ·
                rfl

theorem cell21_1443713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 8].length) (baseStart_1443713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443713 prefixEnd_1443713 := by exact prefixLift 1443713
  have htrace : WordTrace (prefixWord ++ tailWord_1443713) baseStart_1443713 baseEnd_1443713 := by
    simpa [prefixWord, tailWord_1443713, baseEnd_1443713] using wordTrace_append hprefix tailTrace_1443713
  have hstable : (prefixWord ++ tailWord_1443713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443713).length < 2 ^ (prefixWord ++ tailWord_1443713).sum := by decide
  have hdescent : baseEnd_1443713 < baseStart_1443713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443761 : List Nat := [1, 2, 2, 4, 2, 3, 1, 3, 3]
def baseStart_1443761 : Nat := 118140960795 + 1443761 * 2 ^ 59
def prefixEnd_1443761 : Nat := 4983230072969 + 3 ^ 40 * 1443761 * 2
def baseEnd_1443761 : Nat := 329485930318236005399009

theorem tailTrace_1443761 : CollatzResearch.WordTrace tailWord_1443761 prefixEnd_1443761 329485930318236005399009 := by
  unfold tailWord_1443761
  simp only [CollatzResearch.WordTrace]
  refine ⟨52658289722507946593091137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35105526481671964395394091 52658289722507946593091137)
  ·
    refine ⟨39493717291880959944818353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52658289722507946593091137 39493717291880959944818353)
    ·
      refine ⟨29620287968910719958613765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39493717291880959944818353 29620287968910719958613765)
      ·
        refine ⟨5553803994170759992240081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29620287968910719958613765 5553803994170759992240081)
        ·
          refine ⟨4165352995628069994180061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5553803994170759992240081 4165352995628069994180061)
          ·
            refine ⟨1562007373360526247817523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4165352995628069994180061 1562007373360526247817523)
            ·
              refine ⟨2343011060040789371726285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562007373360526247817523 2343011060040789371726285)
              ·
                refine ⟨878629147515296014397357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2343011060040789371726285 878629147515296014397357)
                ·
                  refine ⟨329485930318236005399009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878629147515296014397357 329485930318236005399009)
                  ·
                    rfl

theorem cell21_1443761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 3].length) (baseStart_1443761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1443761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1443761 prefixEnd_1443761 := by exact prefixLift 1443761
  have htrace : WordTrace (prefixWord ++ tailWord_1443761) baseStart_1443761 baseEnd_1443761 := by
    simpa [prefixWord, tailWord_1443761, baseEnd_1443761] using wordTrace_append hprefix tailTrace_1443761
  have hstable : (prefixWord ++ tailWord_1443761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443761).length < 2 ^ (prefixWord ++ tailWord_1443761).sum := by decide
  have hdescent : baseEnd_1443761 < baseStart_1443761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444017 : List Nat := [1, 2, 2, 5, 2, 2, 1, 6]
def baseStart_1444017 : Nat := 118140960795 + 1444017 * 2 ^ 59
def prefixEnd_1444017 : Nat := 4983230072969 + 3 ^ 40 * 1444017 * 2
def baseEnd_1444017 : Nat := 109848117668678816377273

theorem tailTrace_1444017 : CollatzResearch.WordTrace tailWord_1444017 prefixEnd_1444017 109848117668678816377273 := by
  unfold tailWord_1444017
  simp only [CollatzResearch.WordTrace]
  refine ⟨52667626809580502314410305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35111751206387001542940203 52667626809580502314410305)
  ·
    refine ⟨39500720107185376735807729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52667626809580502314410305 39500720107185376735807729)
    ·
      refine ⟨29625540080389032551855797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39500720107185376735807729 29625540080389032551855797)
      ·
        refine ⟨2777394382536471801736481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29625540080389032551855797 2777394382536471801736481)
        ·
          refine ⟨2083045786902353851302361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2777394382536471801736481 2083045786902353851302361)
          ·
            refine ⟨1562284340176765388476771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2083045786902353851302361 1562284340176765388476771)
            ·
              refine ⟨2343426510265148082715157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562284340176765388476771 2343426510265148082715157)
              ·
                refine ⟨109848117668678816377273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2343426510265148082715157 109848117668678816377273)
                ·
                  rfl

theorem cell21_1444017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 6].length) (baseStart_1444017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444017 prefixEnd_1444017 := by exact prefixLift 1444017
  have htrace : WordTrace (prefixWord ++ tailWord_1444017) baseStart_1444017 baseEnd_1444017 := by
    simpa [prefixWord, tailWord_1444017, baseEnd_1444017] using wordTrace_append hprefix tailTrace_1444017
  have hstable : (prefixWord ++ tailWord_1444017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444017).length < 2 ^ (prefixWord ++ tailWord_1444017).sum := by decide
  have hdescent : baseEnd_1444017 < baseStart_1444017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444073 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 9]
def baseStart_1444073 : Nat := 118140960795 + 1444073 * 2 ^ 59
def prefixEnd_1444073 : Nat := 4983230072969 + 3 ^ 40 * 1444073 * 2
def baseEnd_1444073 : Nat := 329557132968992796198371

theorem tailTrace_1444073 : CollatzResearch.WordTrace tailWord_1444073 prefixEnd_1444073 329557132968992796198371 := by
  unfold tailWord_1444073
  simp only [CollatzResearch.WordTrace]
  refine ⟨52669669297377623878448873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35113112864918415918965915 52669669297377623878448873)
  ·
    refine ⟨39502251973033217908836655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52669669297377623878448873 39502251973033217908836655)
    ·
      refine ⟨59253377959549826863254983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39502251973033217908836655 59253377959549826863254983)
      ·
        refine ⟨88880066939324740294882475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59253377959549826863254983 88880066939324740294882475)
        ·
          refine ⟨133320100408987110442323713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88880066939324740294882475 133320100408987110442323713)
          ·
            refine ⟨99990075306740332831742785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133320100408987110442323713 99990075306740332831742785)
            ·
              refine ⟨74992556480055249623807089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99990075306740332831742785 74992556480055249623807089)
              ·
                refine ⟨56244417360041437217855317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74992556480055249623807089 56244417360041437217855317)
                ·
                  refine ⟨329557132968992796198371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56244417360041437217855317 329557132968992796198371)
                  ·
                    rfl

theorem cell21_1444073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_1444073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444073 prefixEnd_1444073 := by exact prefixLift 1444073
  have htrace : WordTrace (prefixWord ++ tailWord_1444073) baseStart_1444073 baseEnd_1444073 := by
    simpa [prefixWord, tailWord_1444073, baseEnd_1444073] using wordTrace_append hprefix tailTrace_1444073
  have hstable : (prefixWord ++ tailWord_1444073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444073).length < 2 ^ (prefixWord ++ tailWord_1444073).sum := by decide
  have hdescent : baseEnd_1444073 < baseStart_1444073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444090 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_1444090 : Nat := 118140960795 + 1444090 * 2 ^ 59
def prefixEnd_1444090 : Nat := 4983230072969 + 3 ^ 40 * 1444090 * 2
def baseEnd_1444090 : Nat := 329561012600604544415003

theorem tailTrace_1444090 : CollatzResearch.WordTrace tailWord_1444090 prefixEnd_1444090 329561012600604544415003 := by
  unfold tailWord_1444090
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167572334579008945454431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35113526225544023854545149 13167572334579008945454431)
  ·
    refine ⟨19751358501868513418181647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13167572334579008945454431 19751358501868513418181647)
    ·
      refine ⟨29627037752802770127272471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19751358501868513418181647 29627037752802770127272471)
      ·
        refine ⟨44440556629204155190908707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29627037752802770127272471 44440556629204155190908707)
        ·
          refine ⟨66660834943806232786363061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44440556629204155190908707 66660834943806232786363061)
          ·
            refine ⟨6249453275981834323721537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66660834943806232786363061 6249453275981834323721537)
            ·
              refine ⟨4687089956986375742791153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6249453275981834323721537 4687089956986375742791153)
              ·
                refine ⟨3515317467739781807093365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687089956986375742791153 3515317467739781807093365)
                ·
                  refine ⟨329561012600604544415003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3515317467739781807093365 329561012600604544415003)
                  ·
                    rfl

theorem cell21_1444090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_1444090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444090 prefixEnd_1444090 := by exact prefixLift 1444090
  have htrace : WordTrace (prefixWord ++ tailWord_1444090) baseStart_1444090 baseEnd_1444090 := by
    simpa [prefixWord, tailWord_1444090, baseEnd_1444090] using wordTrace_append hprefix tailTrace_1444090
  have hstable : (prefixWord ++ tailWord_1444090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444090).length < 2 ^ (prefixWord ++ tailWord_1444090).sum := by decide
  have hdescent : baseEnd_1444090 < baseStart_1444090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444183 : List Nat := [1, 1, 3, 2, 3, 1, 3, 4, 3]
def baseStart_1444183 : Nat := 118140960795 + 1444183 * 2 ^ 59
def prefixEnd_1444183 : Nat := 4983230072969 + 3 ^ 40 * 1444183 * 2
def baseEnd_1444183 : Nat := 329582236467657049364813

theorem tailTrace_1444183 : CollatzResearch.WordTrace tailWord_1444183 prefixEnd_1444183 329582236467657049364813 := by
  unfold tailWord_1444183
  simp only [CollatzResearch.WordTrace]
  refine ⟨52673681326979112664953203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35115787551319408443302135 52673681326979112664953203)
  ·
    refine ⟨79010521990468668997429805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52673681326979112664953203 79010521990468668997429805)
    ·
      refine ⟨29628945746425750874036177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79010521990468668997429805 29628945746425750874036177)
      ·
        refine ⟨22221709309819313155527133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29628945746425750874036177 22221709309819313155527133)
        ·
          refine ⟨8333140991182242433322675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22221709309819313155527133 8333140991182242433322675)
          ·
            refine ⟨12499711486773363649984013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8333140991182242433322675 12499711486773363649984013)
            ·
              refine ⟨4687391807540011368744005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12499711486773363649984013 4687391807540011368744005)
              ·
                refine ⟨878885963913752131639501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4687391807540011368744005 878885963913752131639501)
                ·
                  refine ⟨329582236467657049364813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878885963913752131639501 329582236467657049364813)
                  ·
                    rfl

theorem cell21_1444183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 3].length) (baseStart_1444183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444183 prefixEnd_1444183 := by exact prefixLift 1444183
  have htrace : WordTrace (prefixWord ++ tailWord_1444183) baseStart_1444183 baseEnd_1444183 := by
    simpa [prefixWord, tailWord_1444183, baseEnd_1444183] using wordTrace_append hprefix tailTrace_1444183
  have hstable : (prefixWord ++ tailWord_1444183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444183).length < 2 ^ (prefixWord ++ tailWord_1444183).sum := by decide
  have hdescent : baseEnd_1444183 < baseStart_1444183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444197 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 4]
def baseStart_1444197 : Nat := 118140960795 + 1444197 * 2 ^ 59
def prefixEnd_1444197 : Nat := 4983230072969 + 3 ^ 40 * 1444197 * 2
def baseEnd_1444197 : Nat := 329585431458396136131451

theorem tailTrace_1444197 : CollatzResearch.WordTrace tailWord_1444197 prefixEnd_1444197 329585431458396136131451 := by
  unfold tailWord_1444197
  simp only [CollatzResearch.WordTrace]
  refine ⟨52674191948928393055962845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35116127965952262037308563 52674191948928393055962845)
  ·
    refine ⟨19752821980848147395986067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52674191948928393055962845 19752821980848147395986067)
    ·
      refine ⟨29629232971272221093979101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19752821980848147395986067 29629232971272221093979101)
      ·
        refine ⟨11110962364227082910242163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29629232971272221093979101 11110962364227082910242163)
        ·
          refine ⟨16666443546340624365363245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11110962364227082910242163 16666443546340624365363245)
          ·
            refine ⟨6249916329877734137011217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16666443546340624365363245 6249916329877734137011217)
            ·
              refine ⟨4687437247408300602758413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6249916329877734137011217 4687437247408300602758413)
              ·
                refine ⟨1757788967778112726034405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4687437247408300602758413 1757788967778112726034405)
                ·
                  refine ⟨329585431458396136131451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1757788967778112726034405 329585431458396136131451)
                  ·
                    rfl

theorem cell21_1444197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_1444197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444197 prefixEnd_1444197 := by exact prefixLift 1444197
  have htrace : WordTrace (prefixWord ++ tailWord_1444197) baseStart_1444197 baseEnd_1444197 := by
    simpa [prefixWord, tailWord_1444197, baseEnd_1444197] using wordTrace_append hprefix tailTrace_1444197
  have hstable : (prefixWord ++ tailWord_1444197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444197).length < 2 ^ (prefixWord ++ tailWord_1444197).sum := by decide
  have hdescent : baseEnd_1444197 < baseStart_1444197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444349 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 4]
def baseStart_1444349 : Nat := 118140960795 + 1444349 * 2 ^ 59
def prefixEnd_1444349 : Nat := 4983230072969 + 3 ^ 40 * 1444349 * 2
def baseEnd_1444349 : Nat := 329620119929277649597807

theorem tailTrace_1444349 : CollatzResearch.WordTrace tailWord_1444349 prefixEnd_1444349 329620119929277649597807 := by
  unfold tailWord_1444349
  simp only [CollatzResearch.WordTrace]
  refine ⟨52679735844377723015496101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35119823896251815343664067 52679735844377723015496101)
  ·
    refine ⟨9877450470820823065405519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52679735844377723015496101 9877450470820823065405519)
    ·
      refine ⟨14816175706231234598108279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9877450470820823065405519 14816175706231234598108279)
      ·
        refine ⟨22224263559346851897162419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14816175706231234598108279 22224263559346851897162419)
        ·
          refine ⟨33336395339020277845743629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22224263559346851897162419 33336395339020277845743629)
          ·
            refine ⟨12501148252132604192153861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33336395339020277845743629 12501148252132604192153861)
            ·
              refine ⟨2343965297274863286028849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12501148252132604192153861 2343965297274863286028849)
              ·
                refine ⟨1757973972956147464521637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2343965297274863286028849 1757973972956147464521637)
                ·
                  refine ⟨329620119929277649597807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1757973972956147464521637 329620119929277649597807)
                  ·
                    rfl

theorem cell21_1444349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_1444349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444349 prefixEnd_1444349 := by exact prefixLift 1444349
  have htrace : WordTrace (prefixWord ++ tailWord_1444349) baseStart_1444349 baseEnd_1444349 := by
    simpa [prefixWord, tailWord_1444349, baseEnd_1444349] using wordTrace_append hprefix tailTrace_1444349
  have hstable : (prefixWord ++ tailWord_1444349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444349).length < 2 ^ (prefixWord ++ tailWord_1444349).sum := by decide
  have hdescent : baseEnd_1444349 < baseStart_1444349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444363 : List Nat := [1, 1, 1, 1, 7, 1, 3, 6]
def baseStart_1444363 : Nat := 118140960795 + 1444363 * 2 ^ 59
def prefixEnd_1444363 : Nat := 4983230072969 + 3 ^ 40 * 1444363 * 2
def baseEnd_1444363 : Nat := 109874438306672245454815

theorem tailTrace_1444363 : CollatzResearch.WordTrace tailWord_1444363 prefixEnd_1444363 109874438306672245454815 := by
  unfold tailWord_1444363
  simp only [CollatzResearch.WordTrace]
  refine ⟨52680246466327003406505743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35120164310884668937670495 52680246466327003406505743)
  ·
    refine ⟨79020369699490505109758615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52680246466327003406505743 79020369699490505109758615)
    ·
      refine ⟨118530554549235757664637923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79020369699490505109758615 118530554549235757664637923)
      ·
        refine ⟨177795831823853636496956885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118530554549235757664637923 177795831823853636496956885)
        ·
          refine ⟨4167089808371569605397427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 177795831823853636496956885 4167089808371569605397427)
          ·
            refine ⟨6250634712557354408096141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4167089808371569605397427 6250634712557354408096141)
            ·
              refine ⟨2343988017209007903036053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6250634712557354408096141 2343988017209007903036053)
              ·
                refine ⟨109874438306672245454815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2343988017209007903036053 109874438306672245454815)
                ·
                  rfl

theorem cell21_1444363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 6].length) (baseStart_1444363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444363 prefixEnd_1444363 := by exact prefixLift 1444363
  have htrace : WordTrace (prefixWord ++ tailWord_1444363) baseStart_1444363 baseEnd_1444363 := by
    simpa [prefixWord, tailWord_1444363, baseEnd_1444363] using wordTrace_append hprefix tailTrace_1444363
  have hstable : (prefixWord ++ tailWord_1444363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444363).length < 2 ^ (prefixWord ++ tailWord_1444363).sum := by decide
  have hdescent : baseEnd_1444363 < baseStart_1444363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444377 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 5]
def baseStart_1444377 : Nat := 118140960795 + 1444377 * 2 ^ 59
def prefixEnd_1444377 : Nat := 4983230072969 + 3 ^ 40 * 1444377 * 2
def baseEnd_1444377 : Nat := 329626509910755823131083

theorem tailTrace_1444377 : CollatzResearch.WordTrace tailWord_1444377 prefixEnd_1444377 329626509910755823131083 := by
  unfold tailWord_1444377
  simp only [CollatzResearch.WordTrace]
  refine ⟨52680757088276283797515385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35120504725517522531676923 52680757088276283797515385)
  ·
    refine ⟨39510567816207212848136539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52680757088276283797515385 39510567816207212848136539)
    ·
      refine ⟨59265851724310819272204809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39510567816207212848136539 59265851724310819272204809)
      ·
        refine ⟨44449388793233114454153607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59265851724310819272204809 44449388793233114454153607)
        ·
          refine ⟨66674083189849671681230411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44449388793233114454153607 66674083189849671681230411)
          ·
            refine ⟨100011124784774507521845617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66674083189849671681230411 100011124784774507521845617)
            ·
              refine ⟨75008343588580880641384213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100011124784774507521845617 75008343588580880641384213)
              ·
                refine ⟨3516016105714728780064885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75008343588580880641384213 3516016105714728780064885)
                ·
                  refine ⟨329626509910755823131083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3516016105714728780064885 329626509910755823131083)
                  ·
                    rfl

theorem cell21_1444377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_1444377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444377 prefixEnd_1444377 := by exact prefixLift 1444377
  have htrace : WordTrace (prefixWord ++ tailWord_1444377) baseStart_1444377 baseEnd_1444377 := by
    simpa [prefixWord, tailWord_1444377, baseEnd_1444377] using wordTrace_append hprefix tailTrace_1444377
  have hstable : (prefixWord ++ tailWord_1444377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444377).length < 2 ^ (prefixWord ++ tailWord_1444377).sum := by decide
  have hdescent : baseEnd_1444377 < baseStart_1444377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444380 : List Nat := [2, 2, 3, 1, 2, 3, 3, 5]
def baseStart_1444380 : Nat := 118140960795 + 1444380 * 2 ^ 59
def prefixEnd_1444380 : Nat := 4983230072969 + 3 ^ 40 * 1444380 * 2
def baseEnd_1444380 : Nat := 109875731517209494860359

theorem tailTrace_1444380 : CollatzResearch.WordTrace tailWord_1444380 prefixEnd_1444380 109875731517209494860359 := by
  unfold tailWord_1444380
  simp only [CollatzResearch.WordTrace]
  refine ⟨26340433253632707654937297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35120577671510276873249729 26340433253632707654937297)
  ·
    refine ⟨19755324940224530741202973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26340433253632707654937297 19755324940224530741202973)
    ·
      refine ⟨7408246852584199027951115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19755324940224530741202973 7408246852584199027951115)
      ·
        refine ⟨11112370278876298541926673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7408246852584199027951115 11112370278876298541926673)
        ·
          refine ⟨8334277709157223906445005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11112370278876298541926673 8334277709157223906445005)
          ·
            refine ⟨3125354140933958964916877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8334277709157223906445005 3125354140933958964916877)
            ·
              refine ⟨1172007802850234611843829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3125354140933958964916877 1172007802850234611843829)
              ·
                refine ⟨109875731517209494860359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1172007802850234611843829 109875731517209494860359)
                ·
                  rfl

theorem cell21_1444380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_1444380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444380 prefixEnd_1444380 := by exact prefixLift 1444380
  have htrace : WordTrace (prefixWord ++ tailWord_1444380) baseStart_1444380 baseEnd_1444380 := by
    simpa [prefixWord, tailWord_1444380, baseEnd_1444380] using wordTrace_append hprefix tailTrace_1444380
  have hstable : (prefixWord ++ tailWord_1444380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444380).length < 2 ^ (prefixWord ++ tailWord_1444380).sum := by decide
  have hdescent : baseEnd_1444380 < baseStart_1444380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444408 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_1444408 : Nat := 118140960795 + 1444408 * 2 ^ 59
def prefixEnd_1444408 : Nat := 4983230072969 + 3 ^ 40 * 1444408 * 2
def baseEnd_1444408 : Nat := 329633584533106658114353

theorem tailTrace_1444408 : CollatzResearch.WordTrace tailWord_1444408 prefixEnd_1444408 329633584533106658114353 := by
  unfold tailWord_1444408
  simp only [CollatzResearch.WordTrace]
  refine ⟨26340943875581988045946939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35121258500775984061262585 26340943875581988045946939)
  ·
    refine ⟨39511415813372982068920409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26340943875581988045946939 39511415813372982068920409)
    ·
      refine ⟨29633561860029736551690307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39511415813372982068920409 29633561860029736551690307)
      ·
        refine ⟨44450342790044604827535461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29633561860029736551690307 44450342790044604827535461)
        ·
          refine ⟨8334439273133363405162899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44450342790044604827535461 8334439273133363405162899)
          ·
            refine ⟨12501658909700045107744349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8334439273133363405162899 12501658909700045107744349)
            ·
              refine ⟨4688122091137516915404131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12501658909700045107744349 4688122091137516915404131)
              ·
                refine ⟨7032183136706275373106197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4688122091137516915404131 7032183136706275373106197)
                ·
                  refine ⟨329633584533106658114353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7032183136706275373106197 329633584533106658114353)
                  ·
                    rfl

theorem cell21_1444408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_1444408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444408 prefixEnd_1444408 := by exact prefixLift 1444408
  have htrace : WordTrace (prefixWord ++ tailWord_1444408) baseStart_1444408 baseEnd_1444408 := by
    simpa [prefixWord, tailWord_1444408, baseEnd_1444408] using wordTrace_append hprefix tailTrace_1444408
  have hstable : (prefixWord ++ tailWord_1444408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444408).length < 2 ^ (prefixWord ++ tailWord_1444408).sum := by decide
  have hdescent : baseEnd_1444408 < baseStart_1444408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444456 : List Nat := [2, 1, 4, 3, 2, 2, 7]
def baseStart_1444456 : Nat := 118140960795 + 1444456 * 2 ^ 59
def prefixEnd_1444456 : Nat := 4983230072969 + 3 ^ 40 * 1444456 * 2
def baseEnd_1444456 : Nat := 36627170976341026812695

theorem tailTrace_1444456 : CollatzResearch.WordTrace tailWord_1444456 prefixEnd_1444456 36627170976341026812695 := by
  unfold tailWord_1444456
  simp only [CollatzResearch.WordTrace]
  refine ⟨26341819227495040144820611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35122425636660053526427481 26341819227495040144820611)
  ·
    refine ⟨39512728841242560217230917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26341819227495040144820611 39512728841242560217230917)
    ·
      refine ⟨7408636657732980040730797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39512728841242560217230917 7408636657732980040730797)
      ·
        refine ⟨2778238746649867515274049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7408636657732980040730797 2778238746649867515274049)
        ·
          refine ⟨2083679059987400636455537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2778238746649867515274049 2083679059987400636455537)
          ·
            refine ⟨1562759294990550477341653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2083679059987400636455537 1562759294990550477341653)
            ·
              refine ⟨36627170976341026812695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1562759294990550477341653 36627170976341026812695)
              ·
                rfl

theorem cell21_1444456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 7].length) (baseStart_1444456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444456 prefixEnd_1444456 := by exact prefixLift 1444456
  have htrace : WordTrace (prefixWord ++ tailWord_1444456) baseStart_1444456 baseEnd_1444456 := by
    simpa [prefixWord, tailWord_1444456, baseEnd_1444456] using wordTrace_append hprefix tailTrace_1444456
  have hstable : (prefixWord ++ tailWord_1444456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444456).length < 2 ^ (prefixWord ++ tailWord_1444456).sum := by decide
  have hdescent : baseEnd_1444456 < baseStart_1444456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444577 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 4]
def baseStart_1444577 : Nat := 118140960795 + 1444577 * 2 ^ 59
def prefixEnd_1444577 : Nat := 4983230072969 + 3 ^ 40 * 1444577 * 2
def baseEnd_1444577 : Nat := 329672152635599919797341

theorem tailTrace_1444577 : CollatzResearch.WordTrace tailWord_1444577 prefixEnd_1444577 329672152635599919797341 := by
  unfold tailWord_1444577
  simp only [CollatzResearch.WordTrace]
  refine ⟨52688051687551717954795985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35125367791701145303197323 52688051687551717954795985)
  ·
    refine ⟨39516038765663788466096989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52688051687551717954795985 39516038765663788466096989)
    ·
      refine ⟨14818514537123920674786371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39516038765663788466096989 14818514537123920674786371)
      ·
        refine ⟨22227771805685881012179557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14818514537123920674786371 22227771805685881012179557)
        ·
          refine ⟨4167707213566102689783667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22227771805685881012179557 4167707213566102689783667)
          ·
            refine ⟨6251560820349154034675501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4167707213566102689783667 6251560820349154034675501)
            ·
              refine ⟨2344335307630932763003313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6251560820349154034675501 2344335307630932763003313)
              ·
                refine ⟨1758251480723199572252485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344335307630932763003313 1758251480723199572252485)
                ·
                  refine ⟨329672152635599919797341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1758251480723199572252485 329672152635599919797341)
                  ·
                    rfl

theorem cell21_1444577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_1444577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444577 prefixEnd_1444577 := by exact prefixLift 1444577
  have htrace : WordTrace (prefixWord ++ tailWord_1444577) baseStart_1444577 baseEnd_1444577 := by
    simpa [prefixWord, tailWord_1444577, baseEnd_1444577] using wordTrace_append hprefix tailTrace_1444577
  have hstable : (prefixWord ++ tailWord_1444577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444577).length < 2 ^ (prefixWord ++ tailWord_1444577).sum := by decide
  have hdescent : baseEnd_1444577 < baseStart_1444577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444594 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_1444594 : Nat := 118140960795 + 1444594 * 2 ^ 59
def prefixEnd_1444594 : Nat := 4983230072969 + 3 ^ 40 * 1444594 * 2
def baseEnd_1444594 : Nat := 329676032267211668013973

theorem tailTrace_1444594 : CollatzResearch.WordTrace tailWord_1444594 prefixEnd_1444594 329676032267211668013973 := by
  unfold tailWord_1444594
  simp only [CollatzResearch.WordTrace]
  refine ⟨13172167932122532464541209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35125781152326753238776557 13172167932122532464541209)
  ·
    refine ⟨9879125949091899348405907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13172167932122532464541209 9879125949091899348405907)
    ·
      refine ⟨14818688923637849022608861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9879125949091899348405907 14818688923637849022608861)
      ·
        refine ⟨5557008346364193383478323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14818688923637849022608861 5557008346364193383478323)
        ·
          refine ⟨8335512519546290075217485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5557008346364193383478323 8335512519546290075217485)
          ·
            refine ⟨3125817194829858778206557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8335512519546290075217485 3125817194829858778206557)
            ·
              refine ⟨1172181448061197041827459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3125817194829858778206557 1172181448061197041827459)
              ·
                refine ⟨1758272172091795562741189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172181448061197041827459 1758272172091795562741189)
                ·
                  refine ⟨329676032267211668013973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1758272172091795562741189 329676032267211668013973)
                  ·
                    rfl

theorem cell21_1444594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_1444594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444594 prefixEnd_1444594 := by exact prefixLift 1444594
  have htrace : WordTrace (prefixWord ++ tailWord_1444594) baseStart_1444594 baseEnd_1444594 := by
    simpa [prefixWord, tailWord_1444594, baseEnd_1444594] using wordTrace_append hprefix tailTrace_1444594
  have hstable : (prefixWord ++ tailWord_1444594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444594).length < 2 ^ (prefixWord ++ tailWord_1444594).sum := by decide
  have hdescent : baseEnd_1444594 < baseStart_1444594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444605 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1444605 : Nat := 118140960795 + 1444605 * 2 ^ 59
def prefixEnd_1444605 : Nat := 4983230072969 + 3 ^ 40 * 1444605 * 2
def baseEnd_1444605 : Nat := 329678542617078093330617

theorem tailTrace_1444605 : CollatzResearch.WordTrace tailWord_1444605 prefixEnd_1444605 329678542617078093330617 := by
  unfold tailWord_1444605
  simp only [CollatzResearch.WordTrace]
  refine ⟨52689072931450278736815269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35126048620966852491210179 52689072931450278736815269)
  ·
    refine ⟨9879201174646927263152863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52689072931450278736815269 9879201174646927263152863)
    ·
      refine ⟨14818801761970390894729295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9879201174646927263152863 14818801761970390894729295)
      ·
        refine ⟨22228202642955586342093943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14818801761970390894729295 22228202642955586342093943)
        ·
          refine ⟨33342303964433379513140915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22228202642955586342093943 33342303964433379513140915)
          ·
            refine ⟨50013455946650069269711373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33342303964433379513140915 50013455946650069269711373)
            ·
              refine ⟨18755045979993775976141765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50013455946650069269711373 18755045979993775976141765)
              ·
                refine ⟨3516571121248832995526581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18755045979993775976141765 3516571121248832995526581)
                ·
                  refine ⟨329678542617078093330617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3516571121248832995526581 329678542617078093330617)
                  ·
                    rfl

theorem cell21_1444605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1444605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444605 prefixEnd_1444605 := by exact prefixLift 1444605
  have htrace : WordTrace (prefixWord ++ tailWord_1444605) baseStart_1444605 baseEnd_1444605 := by
    simpa [prefixWord, tailWord_1444605, baseEnd_1444605] using wordTrace_append hprefix tailTrace_1444605
  have hstable : (prefixWord ++ tailWord_1444605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444605).length < 2 ^ (prefixWord ++ tailWord_1444605).sum := by decide
  have hdescent : baseEnd_1444605 < baseStart_1444605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444636 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_1444636 : Nat := 118140960795 + 1444636 * 2 ^ 59
def prefixEnd_1444636 : Nat := 4983230072969 + 3 ^ 40 * 1444636 * 2
def baseEnd_1444636 : Nat := 329685617239428928313887

theorem tailTrace_1444636 : CollatzResearch.WordTrace tailWord_1444636 prefixEnd_1444636 329685617239428928313887 := by
  unfold tailWord_1444636
  simp only [CollatzResearch.WordTrace]
  refine ⟨26345101797168985515596881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35126802396225314020795841 26345101797168985515596881)
  ·
    refine ⟨19758826347876739136697661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26345101797168985515596881 19758826347876739136697661)
    ·
      refine ⟨7409559880453777176261623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19758826347876739136697661 7409559880453777176261623)
      ·
        refine ⟨11114339820680665764392435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7409559880453777176261623 11114339820680665764392435)
        ·
          refine ⟨16671509731020998646588653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11114339820680665764392435 16671509731020998646588653)
          ·
            refine ⟨6251816149132874492470745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16671509731020998646588653 6251816149132874492470745)
            ·
              refine ⟨4688862111849655869353059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6251816149132874492470745 4688862111849655869353059)
              ·
                refine ⟨7033293167774483804029589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4688862111849655869353059 7033293167774483804029589)
                ·
                  refine ⟨329685617239428928313887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7033293167774483804029589 329685617239428928313887)
                  ·
                    rfl

theorem cell21_1444636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_1444636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444636 prefixEnd_1444636 := by exact prefixLift 1444636
  have htrace : WordTrace (prefixWord ++ tailWord_1444636) baseStart_1444636 baseEnd_1444636 := by
    simpa [prefixWord, tailWord_1444636, baseEnd_1444636] using wordTrace_append hprefix tailTrace_1444636
  have hstable : (prefixWord ++ tailWord_1444636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444636).length < 2 ^ (prefixWord ++ tailWord_1444636).sum := by decide
  have hdescent : baseEnd_1444636 < baseStart_1444636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444746 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_1444746 : Nat := 118140960795 + 1444746 * 2 ^ 59
def prefixEnd_1444746 : Nat := 4983230072969 + 3 ^ 40 * 1444746 * 2
def baseEnd_1444746 : Nat := 329710720738093181480329

theorem tailTrace_1444746 : CollatzResearch.WordTrace tailWord_1444746 prefixEnd_1444746 329710720738093181480329 := by
  unfold tailWord_1444746
  simp only [CollatzResearch.WordTrace]
  refine ⟨13173553905984864954424523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35129477082626306545132061 13173553905984864954424523)
  ·
    refine ⟨19760330858977297431636785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13173553905984864954424523 19760330858977297431636785)
    ·
      refine ⟨14820248144232973073727589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19760330858977297431636785 14820248144232973073727589)
      ·
        refine ⟨2778796527043682451323923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14820248144232973073727589 2778796527043682451323923)
        ·
          refine ⟨4168194790565523676985885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778796527043682451323923 4168194790565523676985885)
          ·
            refine ⟨1563073046462071378869707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4168194790565523676985885 1563073046462071378869707)
            ·
              refine ⟨2344609569693107068304561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563073046462071378869707 2344609569693107068304561)
              ·
                refine ⟨1758457177269830301228421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344609569693107068304561 1758457177269830301228421)
                ·
                  refine ⟨329710720738093181480329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1758457177269830301228421 329710720738093181480329)
                  ·
                    rfl

theorem cell21_1444746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_1444746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444746 prefixEnd_1444746 := by exact prefixLift 1444746
  have htrace : WordTrace (prefixWord ++ tailWord_1444746) baseStart_1444746 baseEnd_1444746 := by
    simpa [prefixWord, tailWord_1444746, baseEnd_1444746] using wordTrace_append hprefix tailTrace_1444746
  have hstable : (prefixWord ++ tailWord_1444746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444746).length < 2 ^ (prefixWord ++ tailWord_1444746).sum := by decide
  have hdescent : baseEnd_1444746 < baseStart_1444746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444757 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 5]
def baseStart_1444757 : Nat := 118140960795 + 1444757 * 2 ^ 59
def prefixEnd_1444757 : Nat := 4983230072969 + 3 ^ 40 * 1444757 * 2
def baseEnd_1444757 : Nat := 329713231087959606796973

theorem tailTrace_1444757 : CollatzResearch.WordTrace tailWord_1444757 prefixEnd_1444757 329713231087959606796973 := by
  unfold tailWord_1444757
  simp only [CollatzResearch.WordTrace]
  refine ⟨52694616826899608696348525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35129744551266405797565683 52694616826899608696348525)
  ·
    refine ⟨19760481310087353261130697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52694616826899608696348525 19760481310087353261130697)
    ·
      refine ⟨14820360982565514945848023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19760481310087353261130697 14820360982565514945848023)
      ·
        refine ⟨22230541473848272418772035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14820360982565514945848023 22230541473848272418772035)
        ·
          refine ⟨33345812210772408628158053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22230541473848272418772035 33345812210772408628158053)
          ·
            refine ⟨6252339789519826617779635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33345812210772408628158053 6252339789519826617779635)
            ·
              refine ⟨9378509684279739926669453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6252339789519826617779635 9378509684279739926669453)
              ·
                refine ⟨3516941131604902472501045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9378509684279739926669453 3516941131604902472501045)
                ·
                  refine ⟨329713231087959606796973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3516941131604902472501045 329713231087959606796973)
                  ·
                    rfl

theorem cell21_1444757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_1444757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444757 prefixEnd_1444757 := by exact prefixLift 1444757
  have htrace : WordTrace (prefixWord ++ tailWord_1444757) baseStart_1444757 baseEnd_1444757 := by
    simpa [prefixWord, tailWord_1444757, baseEnd_1444757] using wordTrace_append hprefix tailTrace_1444757
  have hstable : (prefixWord ++ tailWord_1444757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444757).length < 2 ^ (prefixWord ++ tailWord_1444757).sum := by decide
  have hdescent : baseEnd_1444757 < baseStart_1444757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444808 : List Nat := [2, 1, 3, 1, 5, 1, 3, 2, 3]
def baseStart_1444808 : Nat := 118140960795 + 1444808 * 2 ^ 59
def prefixEnd_1444808 : Nat := 4983230072969 + 3 ^ 40 * 1444808 * 2
def baseEnd_1444808 : Nat := 329724869982794851446869

theorem tailTrace_1444808 : CollatzResearch.WordTrace tailWord_1444808 prefixEnd_1444808 329724869982794851446869 := by
  unfold tailWord_1444808
  simp only [CollatzResearch.WordTrace]
  refine ⟨26348238474857422203227539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35130984633143229604303385 26348238474857422203227539)
  ·
    refine ⟨39522357712286133304841309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26348238474857422203227539 39522357712286133304841309)
    ·
      refine ⟨14820884142107299989315491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39522357712286133304841309 14820884142107299989315491)
      ·
        refine ⟨22231326213160949983973237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14820884142107299989315491 22231326213160949983973237)
        ·
          refine ⟨2084186832483839060997491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22231326213160949983973237 2084186832483839060997491)
          ·
            refine ⟨3126280248725758591496237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2084186832483839060997491 3126280248725758591496237)
            ·
              refine ⟨1172355093272159471811089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3126280248725758591496237 1172355093272159471811089)
              ·
                refine ⟨879266319954119603858317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172355093272159471811089 879266319954119603858317)
                ·
                  refine ⟨329724869982794851446869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879266319954119603858317 329724869982794851446869)
                  ·
                    rfl

theorem cell21_1444808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 3].length) (baseStart_1444808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444808 prefixEnd_1444808 := by exact prefixLift 1444808
  have htrace : WordTrace (prefixWord ++ tailWord_1444808) baseStart_1444808 baseEnd_1444808 := by
    simpa [prefixWord, tailWord_1444808, baseEnd_1444808] using wordTrace_append hprefix tailTrace_1444808
  have hstable : (prefixWord ++ tailWord_1444808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444808).length < 2 ^ (prefixWord ++ tailWord_1444808).sum := by decide
  have hdescent : baseEnd_1444808 < baseStart_1444808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444822 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1444822 : Nat := 118140960795 + 1444822 * 2 ^ 59
def prefixEnd_1444822 : Nat := 4983230072969 + 3 ^ 40 * 1444822 * 2
def baseEnd_1444822 : Nat := 329728064973533938213507

theorem tailTrace_1444822 : CollatzResearch.WordTrace tailWord_1444822 prefixEnd_1444822 329728064973533938213507 := by
  unfold tailWord_1444822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293561723229007799841545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35131325047776083198309813 3293561723229007799841545)
  ·
    refine ⟨2470171292421755849881159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3293561723229007799841545 2470171292421755849881159)
    ·
      refine ⟨3705256938632633774821739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2470171292421755849881159 3705256938632633774821739)
      ·
        refine ⟨5557885407948950662232609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3705256938632633774821739 5557885407948950662232609)
        ·
          refine ⟨4168414055961712996674457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5557885407948950662232609 4168414055961712996674457)
          ·
            refine ⟨3126310541971284747505843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4168414055961712996674457 3126310541971284747505843)
            ·
              refine ⟨4689465812956927121258765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3126310541971284747505843 4689465812956927121258765)
              ·
                refine ⟨1758549679858847670472037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4689465812956927121258765 1758549679858847670472037)
                ·
                  refine ⟨329728064973533938213507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1758549679858847670472037 329728064973533938213507)
                  ·
                    rfl

theorem cell21_1444822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1444822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444822 prefixEnd_1444822 := by exact prefixLift 1444822
  have htrace : WordTrace (prefixWord ++ tailWord_1444822) baseStart_1444822 baseEnd_1444822 := by
    simpa [prefixWord, tailWord_1444822, baseEnd_1444822] using wordTrace_append hprefix tailTrace_1444822
  have hstable : (prefixWord ++ tailWord_1444822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444822).length < 2 ^ (prefixWord ++ tailWord_1444822).sum := by decide
  have hdescent : baseEnd_1444822 < baseStart_1444822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444895 : List Nat := [1, 1, 2, 4, 1, 4, 3, 5]
def baseStart_1444895 : Nat := 118140960795 + 1444895 * 2 ^ 59
def prefixEnd_1444895 : Nat := 4983230072969 + 3 ^ 40 * 1444895 * 2
def baseEnd_1444895 : Nat := 109914908189367344498897

theorem tailTrace_1444895 : CollatzResearch.WordTrace tailWord_1444895 prefixEnd_1444895 109914908189367344498897 := by
  unfold tailWord_1444895
  simp only [CollatzResearch.WordTrace]
  refine ⟨52699650100399658264872139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35133100066933105509914759 52699650100399658264872139)
  ·
    refine ⟨79049475150599487397308209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52699650100399658264872139 79049475150599487397308209)
    ·
      refine ⟨59287106362949615547981157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79049475150599487397308209 59287106362949615547981157)
      ·
        refine ⟨11116332443053052915246467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59287106362949615547981157 11116332443053052915246467)
        ·
          refine ⟨16674498664579579372869701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11116332443053052915246467 16674498664579579372869701)
          ·
            refine ⟨3126468499608671132413069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16674498664579579372869701 3126468499608671132413069)
            ·
              refine ⟨1172425687353251674654901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3126468499608671132413069 1172425687353251674654901)
              ·
                refine ⟨109914908189367344498897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1172425687353251674654901 109914908189367344498897)
                ·
                  rfl

theorem cell21_1444895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 5].length) (baseStart_1444895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444895 prefixEnd_1444895 := by exact prefixLift 1444895
  have htrace : WordTrace (prefixWord ++ tailWord_1444895) baseStart_1444895 baseEnd_1444895 := by
    simpa [prefixWord, tailWord_1444895, baseEnd_1444895] using wordTrace_append hprefix tailTrace_1444895
  have hstable : (prefixWord ++ tailWord_1444895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444895).length < 2 ^ (prefixWord ++ tailWord_1444895).sum := by decide
  have hdescent : baseEnd_1444895 < baseStart_1444895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1444926 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1444926 : Nat := 118140960795 + 1444926 * 2 ^ 59
def prefixEnd_1444926 : Nat := 4983230072969 + 3 ^ 40 * 1444926 * 2
def baseEnd_1444926 : Nat := 329751799190452868479961

theorem tailTrace_1444926 : CollatzResearch.WordTrace tailWord_1444926 prefixEnd_1444926 329751799190452868479961 := by
  unfold tailWord_1444926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6587597595410918819906329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35133853842191567039500421 6587597595410918819906329)
  ·
    refine ⟨4940698196558189114929747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6587597595410918819906329 4940698196558189114929747)
    ·
      refine ⟨7411047294837283672394621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4940698196558189114929747 7411047294837283672394621)
      ·
        refine ⟨2779142735563981377147983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7411047294837283672394621 2779142735563981377147983)
        ·
          refine ⟨4168714103345972065721975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779142735563981377147983 4168714103345972065721975)
          ·
            refine ⟨6253071155018958098582963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168714103345972065721975 6253071155018958098582963)
            ·
              refine ⟨9379606732528437147874445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6253071155018958098582963 9379606732528437147874445)
              ·
                refine ⟨3517352524698163930452917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9379606732528437147874445 3517352524698163930452917)
                ·
                  refine ⟨329751799190452868479961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3517352524698163930452917 329751799190452868479961)
                  ·
                    rfl

theorem cell21_1444926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1444926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1444926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1444926 prefixEnd_1444926 := by exact prefixLift 1444926
  have htrace : WordTrace (prefixWord ++ tailWord_1444926) baseStart_1444926 baseEnd_1444926 := by
    simpa [prefixWord, tailWord_1444926, baseEnd_1444926] using wordTrace_append hprefix tailTrace_1444926
  have hstable : (prefixWord ++ tailWord_1444926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1444926).length < 2 ^ (prefixWord ++ tailWord_1444926).sum := by decide
  have hdescent : baseEnd_1444926 < baseStart_1444926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1444926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445092 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 4]
def baseStart_1445092 : Nat := 118140960795 + 1445092 * 2 ^ 59
def prefixEnd_1445092 : Nat := 4983230072969 + 3 ^ 40 * 1445092 * 2
def baseEnd_1445092 : Nat := 329789682652073468712955

theorem tailTrace_1445092 : CollatzResearch.WordTrace tailWord_1445092 prefixEnd_1445092 329789682652073468712955 := by
  unfold tailWord_1445092
  simp only [CollatzResearch.WordTrace]
  refine ⟨26353417640342980454896765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35137890187123973939862353 26353417640342980454896765)
  ·
    refine ⟨9882531615128617670586287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26353417640342980454896765 9882531615128617670586287)
    ·
      refine ⟨14823797422692926505879431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9882531615128617670586287 14823797422692926505879431)
      ·
        refine ⟨22235696134039389758819147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14823797422692926505879431 22235696134039389758819147)
        ·
          refine ⟨33353544201059084638228721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22235696134039389758819147 33353544201059084638228721)
          ·
            refine ⟨25015158150794313478671541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33353544201059084638228721 25015158150794313478671541)
            ·
              refine ⟨2345171076636966888625457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25015158150794313478671541 2345171076636966888625457)
              ·
                refine ⟨1758878307477725166469093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2345171076636966888625457 1758878307477725166469093)
                ·
                  refine ⟨329789682652073468712955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1758878307477725166469093 329789682652073468712955)
                  ·
                    rfl

theorem cell21_1445092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_1445092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445092 prefixEnd_1445092 := by exact prefixLift 1445092
  have htrace : WordTrace (prefixWord ++ tailWord_1445092) baseStart_1445092 baseEnd_1445092 := by
    simpa [prefixWord, tailWord_1445092, baseEnd_1445092] using wordTrace_append hprefix tailTrace_1445092
  have hstable : (prefixWord ++ tailWord_1445092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445092).length < 2 ^ (prefixWord ++ tailWord_1445092).sum := by decide
  have hdescent : baseEnd_1445092 < baseStart_1445092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445123 : List Nat := [1, 1, 1, 3, 2, 6, 2, 5]
def baseStart_1445123 : Nat := 118140960795 + 1445123 * 2 ^ 59
def prefixEnd_1445123 : Nat := 4983230072969 + 3 ^ 40 * 1445123 * 2
def baseEnd_1445123 : Nat := 109932252424808101232075

theorem tailTrace_1445123 : CollatzResearch.WordTrace tailWord_1445123 prefixEnd_1445123 109932252424808101232075 := by
  unfold tailWord_1445123
  simp only [CollatzResearch.WordTrace]
  refine ⟨52707965943573653204172023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35138643962382435469448015 52707965943573653204172023)
  ·
    refine ⟨79061948915360479806258035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52707965943573653204172023 79061948915360479806258035)
    ·
      refine ⟨118592923373040719709387053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79061948915360479806258035 118592923373040719709387053)
      ·
        refine ⟨44472346264890269891020145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118592923373040719709387053 44472346264890269891020145)
        ·
          refine ⟨33354259698667702418265109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44472346264890269891020145 33354259698667702418265109)
          ·
            refine ⟨1563480923375048550856177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33354259698667702418265109 1563480923375048550856177)
            ·
              refine ⟨1172610692531286413142133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563480923375048550856177 1172610692531286413142133)
              ·
                refine ⟨109932252424808101232075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1172610692531286413142133 109932252424808101232075)
                ·
                  rfl

theorem cell21_1445123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 5].length) (baseStart_1445123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445123 prefixEnd_1445123 := by exact prefixLift 1445123
  have htrace : WordTrace (prefixWord ++ tailWord_1445123) baseStart_1445123 baseEnd_1445123 := by
    simpa [prefixWord, tailWord_1445123, baseEnd_1445123] using wordTrace_append hprefix tailTrace_1445123
  have hstable : (prefixWord ++ tailWord_1445123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445123).length < 2 ^ (prefixWord ++ tailWord_1445123).sum := by decide
  have hdescent : baseEnd_1445123 < baseStart_1445123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445182 : List Nat := [4, 2, 1, 2, 1, 1, 1, 9]
def baseStart_1445182 : Nat := 118140960795 + 1445182 * 2 ^ 59
def prefixEnd_1445182 : Nat := 4983230072969 + 3 ^ 40 * 1445182 * 2
def baseEnd_1445182 : Nat := 109936740626084437404257

theorem tailTrace_1445182 : CollatzResearch.WordTrace tailWord_1445182 prefixEnd_1445182 109936740626084437404257 := by
  unfold tailWord_1445182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6588764731294988285071225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35140078566906604187046533 6588764731294988285071225)
  ·
    refine ⟨4941573548471241213803419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6588764731294988285071225 4941573548471241213803419)
    ·
      refine ⟨7412360322706861820705129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4941573548471241213803419 7412360322706861820705129)
      ·
        refine ⟨5559270242030146365528847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7412360322706861820705129 5559270242030146365528847)
        ·
          refine ⟨8338905363045219548293271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5559270242030146365528847 8338905363045219548293271)
          ·
            refine ⟨12508358044567829322439907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8338905363045219548293271 12508358044567829322439907)
            ·
              refine ⟨18762537066851743983659861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12508358044567829322439907 18762537066851743983659861)
              ·
                refine ⟨109936740626084437404257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18762537066851743983659861 109936740626084437404257)
                ·
                  rfl

theorem cell21_1445182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_1445182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445182 prefixEnd_1445182 := by exact prefixLift 1445182
  have htrace : WordTrace (prefixWord ++ tailWord_1445182) baseStart_1445182 baseEnd_1445182 := by
    simpa [prefixWord, tailWord_1445182, baseEnd_1445182] using wordTrace_append hprefix tailTrace_1445182
  have hstable : (prefixWord ++ tailWord_1445182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445182).length < 2 ^ (prefixWord ++ tailWord_1445182).sum := by decide
  have hdescent : baseEnd_1445182 < baseStart_1445182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445241 : List Nat := [1, 2, 1, 3, 2, 1, 2, 9]
def baseStart_1445241 : Nat := 118140960795 + 1445241 * 2 ^ 59
def prefixEnd_1445241 : Nat := 4983230072969 + 3 ^ 40 * 1445241 * 2
def baseEnd_1445241 : Nat := 109941228827360773576439

theorem tailTrace_1445241 : CollatzResearch.WordTrace tailWord_1445241 prefixEnd_1445241 109941228827360773576439 := by
  unfold tailWord_1445241
  simp only [CollatzResearch.WordTrace]
  refine ⟨52712269757146159356967577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35141513171430772904645051 52712269757146159356967577)
  ·
    refine ⟨39534202317859619517725683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52712269757146159356967577 39534202317859619517725683)
    ·
      refine ⟨59301303476789429276588525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39534202317859619517725683 59301303476789429276588525)
      ·
        refine ⟨22237988803796035978720697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59301303476789429276588525 22237988803796035978720697)
        ·
          refine ⟨16678491602847026984040523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22237988803796035978720697 16678491602847026984040523)
          ·
            refine ⟨25017737404270540476060785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16678491602847026984040523 25017737404270540476060785)
            ·
              refine ⟨18763303053202905357045589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25017737404270540476060785 18763303053202905357045589)
              ·
                refine ⟨109941228827360773576439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18763303053202905357045589 109941228827360773576439)
                ·
                  rfl

theorem cell21_1445241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 9].length) (baseStart_1445241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445241 prefixEnd_1445241 := by exact prefixLift 1445241
  have htrace : WordTrace (prefixWord ++ tailWord_1445241) baseStart_1445241 baseEnd_1445241 := by
    simpa [prefixWord, tailWord_1445241, baseEnd_1445241] using wordTrace_append hprefix tailTrace_1445241
  have hstable : (prefixWord ++ tailWord_1445241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445241).length < 2 ^ (prefixWord ++ tailWord_1445241).sum := by decide
  have hdescent : baseEnd_1445241 < baseStart_1445241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445337 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 4]
def baseStart_1445337 : Nat := 118140960795 + 1445337 * 2 ^ 59
def prefixEnd_1445337 : Nat := 4983230072969 + 3 ^ 40 * 1445337 * 2
def baseEnd_1445337 : Nat := 329845594990007487129121

theorem tailTrace_1445337 : CollatzResearch.WordTrace tailWord_1445337 prefixEnd_1445337 329845594990007487129121 := by
  unfold tailWord_1445337
  simp only [CollatzResearch.WordTrace]
  refine ⟨52715771164798367752462265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35143847443198911834974843 52715771164798367752462265)
  ·
    refine ⟨39536828373598775814346699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52715771164798367752462265 39536828373598775814346699)
    ·
      refine ⟨59305242560398163721520049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39536828373598775814346699 59305242560398163721520049)
      ·
        refine ⟨44478931920298622791140037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59305242560398163721520049 44478931920298622791140037)
        ·
          refine ⟨8339799735055991773338757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44478931920298622791140037 8339799735055991773338757)
          ·
            refine ⟨1563712450322998457501017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8339799735055991773338757 1563712450322998457501017)
            ·
              refine ⟨1172784337742248843125763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563712450322998457501017 1172784337742248843125763)
              ·
                refine ⟨1759176506613373264688645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172784337742248843125763 1759176506613373264688645)
                ·
                  refine ⟨329845594990007487129121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1759176506613373264688645 329845594990007487129121)
                  ·
                    rfl

theorem cell21_1445337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_1445337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445337 prefixEnd_1445337 := by exact prefixLift 1445337
  have htrace : WordTrace (prefixWord ++ tailWord_1445337) baseStart_1445337 baseEnd_1445337 := by
    simpa [prefixWord, tailWord_1445337, baseEnd_1445337] using wordTrace_append hprefix tailTrace_1445337
  have hstable : (prefixWord ++ tailWord_1445337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445337).length < 2 ^ (prefixWord ++ tailWord_1445337).sum := by decide
  have hdescent : baseEnd_1445337 < baseStart_1445337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445348 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_1445348 : Nat := 118140960795 + 1445348 * 2 ^ 59
def prefixEnd_1445348 : Nat := 4983230072969 + 3 ^ 40 * 1445348 * 2
def baseEnd_1445348 : Nat := 329848105339873912445765

theorem tailTrace_1445348 : CollatzResearch.WordTrace tailWord_1445348 prefixEnd_1445348 329848105339873912445765 := by
  unfold tailWord_1445348
  simp only [CollatzResearch.WordTrace]
  refine ⟨26358086183879258315556349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35144114911839011087408465 26358086183879258315556349)
  ·
    refine ⟨9884282318954721868333631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26358086183879258315556349 9884282318954721868333631)
    ·
      refine ⟨14826423478432082802500447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9884282318954721868333631 14826423478432082802500447)
      ·
        refine ⟨22239635217648124203750671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14826423478432082802500447 22239635217648124203750671)
        ·
          refine ⟨33359452826472186305626007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22239635217648124203750671 33359452826472186305626007)
          ·
            refine ⟨50039179239708279458439011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33359452826472186305626007 50039179239708279458439011)
            ·
              refine ⟨75058768859562419187658517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50039179239708279458439011 75058768859562419187658517)
              ·
                refine ⟨3518379790291988399421493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75058768859562419187658517 3518379790291988399421493)
                ·
                  refine ⟨329848105339873912445765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3518379790291988399421493 329848105339873912445765)
                  ·
                    rfl

theorem cell21_1445348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_1445348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445348 prefixEnd_1445348 := by exact prefixLift 1445348
  have htrace : WordTrace (prefixWord ++ tailWord_1445348) baseStart_1445348 baseEnd_1445348 := by
    simpa [prefixWord, tailWord_1445348, baseEnd_1445348] using wordTrace_append hprefix tailTrace_1445348
  have hstable : (prefixWord ++ tailWord_1445348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445348).length < 2 ^ (prefixWord ++ tailWord_1445348).sum := by decide
  have hdescent : baseEnd_1445348 < baseStart_1445348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445374 : List Nat := [4, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_1445374 : Nat := 118140960795 + 1445374 * 2 ^ 59
def prefixEnd_1445374 : Nat := 4983230072969 + 3 ^ 40 * 1445374 * 2
def baseEnd_1445374 : Nat := 329854038894103645012379

theorem tailTrace_1445374 : CollatzResearch.WordTrace tailWord_1445374 prefixEnd_1445374 329854038894103645012379 := by
  unfold tailWord_1445374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6589640083208040383944897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35144747110442882047706117 6589640083208040383944897)
  ·
    refine ⟨4942230062406030287958673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6589640083208040383944897 4942230062406030287958673)
    ·
      refine ⟨3706672546804522715969005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4942230062406030287958673 3706672546804522715969005)
      ·
        refine ⟨1390002205051696018488377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3706672546804522715969005 1390002205051696018488377)
        ·
          refine ⟨1042501653788772013866283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1390002205051696018488377 1042501653788772013866283)
          ·
            refine ⟨1563752480683158020799425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042501653788772013866283 1563752480683158020799425)
            ·
              refine ⟨1172814360512368515599569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563752480683158020799425 1172814360512368515599569)
              ·
                refine ⟨879610770384276386699677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172814360512368515599569 879610770384276386699677)
                ·
                  refine ⟨329854038894103645012379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879610770384276386699677 329854038894103645012379)
                  ·
                    rfl

theorem cell21_1445374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_1445374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445374 prefixEnd_1445374 := by exact prefixLift 1445374
  have htrace : WordTrace (prefixWord ++ tailWord_1445374) baseStart_1445374 baseEnd_1445374 := by
    simpa [prefixWord, tailWord_1445374, baseEnd_1445374] using wordTrace_append hprefix tailTrace_1445374
  have hstable : (prefixWord ++ tailWord_1445374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445374).length < 2 ^ (prefixWord ++ tailWord_1445374).sum := by decide
  have hdescent : baseEnd_1445374 < baseStart_1445374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445430 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_1445430 : Nat := 118140960795 + 1445430 * 2 ^ 59
def prefixEnd_1445430 : Nat := 4983230072969 + 3 ^ 40 * 1445430 * 2
def baseEnd_1445430 : Nat := 329866818857059992078931

theorem tailTrace_1445430 : CollatzResearch.WordTrace tailWord_1445430 prefixEnd_1445430 329866818857059992078931 := by
  unfold tailWord_1445430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3294947697091340289724859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35146108768974296423731829 3294947697091340289724859)
  ·
    refine ⟨4942421545637010434587289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3294947697091340289724859 4942421545637010434587289)
    ·
      refine ⟨3706816159227757825940467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4942421545637010434587289 3706816159227757825940467)
      ·
        refine ⟨5560224238841636738910701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3706816159227757825940467 5560224238841636738910701)
        ·
          refine ⟨2085084089565613777091513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5560224238841636738910701 2085084089565613777091513)
          ·
            refine ⟨1563813067174210332818635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2085084089565613777091513 1563813067174210332818635)
            ·
              refine ⟨2345719600761315499227953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563813067174210332818635 2345719600761315499227953)
              ·
                refine ⟨1759289700570986624420965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2345719600761315499227953 1759289700570986624420965)
                ·
                  refine ⟨329866818857059992078931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1759289700570986624420965 329866818857059992078931)
                  ·
                    rfl

theorem cell21_1445430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_1445430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445430 prefixEnd_1445430 := by exact prefixLift 1445430
  have htrace : WordTrace (prefixWord ++ tailWord_1445430) baseStart_1445430 baseEnd_1445430 := by
    simpa [prefixWord, tailWord_1445430, baseEnd_1445430] using wordTrace_append hprefix tailTrace_1445430
  have hstable : (prefixWord ++ tailWord_1445430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445430).length < 2 ^ (prefixWord ++ tailWord_1445430).sum := by decide
  have hdescent : baseEnd_1445430 < baseStart_1445430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445441 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 5]
def baseStart_1445441 : Nat := 118140960795 + 1445441 * 2 ^ 59
def prefixEnd_1445441 : Nat := 4983230072969 + 3 ^ 40 * 1445441 * 2
def baseEnd_1445441 : Nat := 329869329206926417395575

theorem tailTrace_1445441 : CollatzResearch.WordTrace tailWord_1445441 prefixEnd_1445441 329869329206926417395575 := by
  unfold tailWord_1445441
  simp only [CollatzResearch.WordTrace]
  refine ⟨52719564356421593514248177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35146376237614395676165451 52719564356421593514248177)
  ·
    refine ⟨39539673267316195135686133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52719564356421593514248177 39539673267316195135686133)
    ·
      refine ⟨3706844368810893293970575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39539673267316195135686133 3706844368810893293970575)
      ·
        refine ⟨5560266553216339940955863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3706844368810893293970575 5560266553216339940955863)
        ·
          refine ⟨8340399829824509911433795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5560266553216339940955863 8340399829824509911433795)
          ·
            refine ⟨12510599744736764867150693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8340399829824509911433795 12510599744736764867150693)
            ·
              refine ⟨2345737452138143412590755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12510599744736764867150693 2345737452138143412590755)
              ·
                refine ⟨3518606178207215118886133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345737452138143412590755 3518606178207215118886133)
                ·
                  refine ⟨329869329206926417395575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3518606178207215118886133 329869329206926417395575)
                  ·
                    rfl

theorem cell21_1445441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_1445441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445441 prefixEnd_1445441 := by exact prefixLift 1445441
  have htrace : WordTrace (prefixWord ++ tailWord_1445441) baseStart_1445441 baseEnd_1445441 := by
    simpa [prefixWord, tailWord_1445441, baseEnd_1445441] using wordTrace_append hprefix tailTrace_1445441
  have hstable : (prefixWord ++ tailWord_1445441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445441).length < 2 ^ (prefixWord ++ tailWord_1445441).sum := by decide
  have hdescent : baseEnd_1445441 < baseStart_1445441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445562 : List Nat := [3, 1, 1, 1, 2, 6, 1, 6]
def baseStart_1445562 : Nat := 118140960795 + 1445562 * 2 ^ 59
def prefixEnd_1445562 : Nat := 4983230072969 + 3 ^ 40 * 1445562 * 2
def baseEnd_1445562 : Nat := 109965647685152365292887

theorem tailTrace_1445562 : CollatzResearch.WordTrace tailWord_1445562 prefixEnd_1445562 109965647685152365292887 := by
  unfold tailWord_1445562
  simp only [CollatzResearch.WordTrace]
  refine ⟨13180994397245807794850735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35149318392655487452935293 13180994397245807794850735)
  ·
    refine ⟨19771491595868711692276103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13180994397245807794850735 19771491595868711692276103)
    ·
      refine ⟨29657237393803067538414155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19771491595868711692276103 29657237393803067538414155)
      ·
        refine ⟨44485856090704601307621233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29657237393803067538414155 44485856090704601307621233)
        ·
          refine ⟨33364392068028450980715925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44485856090704601307621233 33364392068028450980715925)
          ·
            refine ⟨1563955878188833639721059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33364392068028450980715925 1563955878188833639721059)
            ·
              refine ⟨2345933817283250459581589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563955878188833639721059 2345933817283250459581589)
              ·
                refine ⟨109965647685152365292887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2345933817283250459581589 109965647685152365292887)
                ·
                  rfl

theorem cell21_1445562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_1445562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445562 prefixEnd_1445562 := by exact prefixLift 1445562
  have htrace : WordTrace (prefixWord ++ tailWord_1445562) baseStart_1445562 baseEnd_1445562 := by
    simpa [prefixWord, tailWord_1445562, baseEnd_1445562] using wordTrace_append hprefix tailTrace_1445562
  have hstable : (prefixWord ++ tailWord_1445562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445562).length < 2 ^ (prefixWord ++ tailWord_1445562).sum := by decide
  have hdescent : baseEnd_1445562 < baseStart_1445562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445576 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_1445576 : Nat := 118140960795 + 1445576 * 2 ^ 59
def prefixEnd_1445576 : Nat := 4983230072969 + 3 ^ 40 * 1445576 * 2
def baseEnd_1445576 : Nat := 329900138046196182645299

theorem tailTrace_1445576 : CollatzResearch.WordTrace tailWord_1445576 prefixEnd_1445576 329900138046196182645299 := by
  unfold tailWord_1445576
  simp only [CollatzResearch.WordTrace]
  refine ⟨26362244105466255785206291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35149658807288341046941721 26362244105466255785206291)
  ·
    refine ⟨39543366158199383677809437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26362244105466255785206291 39543366158199383677809437)
    ·
      refine ⟨14828762309324768879178539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39543366158199383677809437 14828762309324768879178539)
      ·
        refine ⟨22243143463987153318767809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14828762309324768879178539 22243143463987153318767809)
        ·
          refine ⟨16682357597990364989075857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22243143463987153318767809 16682357597990364989075857)
          ·
            refine ⟨12511768198492773741806893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16682357597990364989075857 12511768198492773741806893)
            ·
              refine ⟨4691913074434790153177585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12511768198492773741806893 4691913074434790153177585)
              ·
                refine ⟨3518934805826092614883189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4691913074434790153177585 3518934805826092614883189)
                ·
                  refine ⟨329900138046196182645299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3518934805826092614883189 329900138046196182645299)
                  ·
                    rfl

theorem cell21_1445576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_1445576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445576 prefixEnd_1445576 := by exact prefixLift 1445576
  have htrace : WordTrace (prefixWord ++ tailWord_1445576) baseStart_1445576 baseEnd_1445576 := by
    simpa [prefixWord, tailWord_1445576, baseEnd_1445576] using wordTrace_append hprefix tailTrace_1445576
  have hstable : (prefixWord ++ tailWord_1445576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445576).length < 2 ^ (prefixWord ++ tailWord_1445576).sum := by decide
  have hdescent : baseEnd_1445576 < baseStart_1445576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445593 : List Nat := [1, 2, 1, 2, 3, 3, 1, 5, 3]
def baseStart_1445593 : Nat := 118140960795 + 1445593 * 2 ^ 59
def prefixEnd_1445593 : Nat := 4983230072969 + 3 ^ 40 * 1445593 * 2
def baseEnd_1445593 : Nat := 329904017677807930861931

theorem tailTrace_1445593 : CollatzResearch.WordTrace tailWord_1445593 prefixEnd_1445593 329904017677807930861931 := by
  unfold tailWord_1445593
  simp only [CollatzResearch.WordTrace]
  refine ⟨52725108251870923473781433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35150072167913948982520955 52725108251870923473781433)
  ·
    refine ⟨39543831188903192605336075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52725108251870923473781433 39543831188903192605336075)
    ·
      refine ⟨59315746783354788908004113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39543831188903192605336075 59315746783354788908004113)
      ·
        refine ⟨44486810087516091681003085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59315746783354788908004113 44486810087516091681003085)
        ·
          refine ⟨16682553782818534380376157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44486810087516091681003085 16682553782818534380376157)
          ·
            refine ⟨6255957668556950392641059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16682553782818534380376157 6255957668556950392641059)
            ·
              refine ⟨9383936502835425588961589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6255957668556950392641059 9383936502835425588961589)
              ·
                refine ⟨879744047140821148965149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9383936502835425588961589 879744047140821148965149)
                ·
                  refine ⟨329904017677807930861931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879744047140821148965149 329904017677807930861931)
                  ·
                    rfl

theorem cell21_1445593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 3].length) (baseStart_1445593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445593 prefixEnd_1445593 := by exact prefixLift 1445593
  have htrace : WordTrace (prefixWord ++ tailWord_1445593) baseStart_1445593 baseEnd_1445593 := by
    simpa [prefixWord, tailWord_1445593, baseEnd_1445593] using wordTrace_append hprefix tailTrace_1445593
  have hstable : (prefixWord ++ tailWord_1445593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445593).length < 2 ^ (prefixWord ++ tailWord_1445593).sum := by decide
  have hdescent : baseEnd_1445593 < baseStart_1445593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445669 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 5]
def baseStart_1445669 : Nat := 118140960795 + 1445669 * 2 ^ 59
def prefixEnd_1445669 : Nat := 4983230072969 + 3 ^ 40 * 1445669 * 2
def baseEnd_1445669 : Nat := 329921361913248687595109

theorem tailTrace_1445669 : CollatzResearch.WordTrace tailWord_1445669 prefixEnd_1445669 329921361913248687595109 := by
  unfold tailWord_1445669
  simp only [CollatzResearch.WordTrace]
  refine ⟨52727880199595588453548061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35151920133063725635698707 52727880199595588453548061)
  ·
    refine ⟨19772955074848345670080523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52727880199595588453548061 19772955074848345670080523)
    ·
      refine ⟨29659432612272518505120785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19772955074848345670080523 29659432612272518505120785)
      ·
        refine ⟨22244574459204388878840589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29659432612272518505120785 22244574459204388878840589)
        ·
          refine ⟨8341715422201645829565221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22244574459204388878840589 8341715422201645829565221)
          ·
            refine ⟨1564071641662808593043479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8341715422201645829565221 1564071641662808593043479)
            ·
              refine ⟨2346107462494212889565219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564071641662808593043479 2346107462494212889565219)
              ·
                refine ⟨3519161193741319334347829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2346107462494212889565219 3519161193741319334347829)
                ·
                  refine ⟨329921361913248687595109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3519161193741319334347829 329921361913248687595109)
                  ·
                    rfl

theorem cell21_1445669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_1445669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445669 prefixEnd_1445669 := by exact prefixLift 1445669
  have htrace : WordTrace (prefixWord ++ tailWord_1445669) baseStart_1445669 baseEnd_1445669 := by
    simpa [prefixWord, tailWord_1445669, baseEnd_1445669] using wordTrace_append hprefix tailTrace_1445669
  have hstable : (prefixWord ++ tailWord_1445669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445669).length < 2 ^ (prefixWord ++ tailWord_1445669).sum := by decide
  have hdescent : baseEnd_1445669 < baseStart_1445669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445731 : List Nat := [1, 1, 1, 5, 5, 1, 1, 6]
def baseStart_1445731 : Nat := 118140960795 + 1445731 * 2 ^ 59
def prefixEnd_1445731 : Nat := 4983230072969 + 3 ^ 40 * 1445731 * 2
def baseEnd_1445731 : Nat := 109978503719316785853883

theorem tailTrace_1445731 : CollatzResearch.WordTrace tailWord_1445731 prefixEnd_1445731 109978503719316785853883 := by
  unfold tailWord_1445731
  simp only [CollatzResearch.WordTrace]
  refine ⟨52730141525370973042305047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35153427683580648694870031 52730141525370973042305047)
  ·
    refine ⟨79095212288056459563457571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52730141525370973042305047 79095212288056459563457571)
    ·
      refine ⟨118642818432084689345186357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79095212288056459563457571 118642818432084689345186357)
      ·
        refine ⟨11122764228007939626111221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118642818432084689345186357 11122764228007939626111221)
        ·
          refine ⟨1042759146375744339947927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11122764228007939626111221 1042759146375744339947927)
          ·
            refine ⟨1564138719563616509921891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042759146375744339947927 1564138719563616509921891)
            ·
              refine ⟨2346208079345424764882837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564138719563616509921891 2346208079345424764882837)
              ·
                refine ⟨109978503719316785853883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2346208079345424764882837 109978503719316785853883)
                ·
                  rfl

theorem cell21_1445731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 6].length) (baseStart_1445731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445731 prefixEnd_1445731 := by exact prefixLift 1445731
  have htrace : WordTrace (prefixWord ++ tailWord_1445731) baseStart_1445731 baseEnd_1445731 := by
    simpa [prefixWord, tailWord_1445731, baseEnd_1445731] using wordTrace_append hprefix tailTrace_1445731
  have hstable : (prefixWord ++ tailWord_1445731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445731).length < 2 ^ (prefixWord ++ tailWord_1445731).sum := by decide
  have hdescent : baseEnd_1445731 < baseStart_1445731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445793 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 4]
def baseStart_1445793 : Nat := 118140960795 + 1445793 * 2 ^ 59
def prefixEnd_1445793 : Nat := 4983230072969 + 3 ^ 40 * 1445793 * 2
def baseEnd_1445793 : Nat := 329949660402652027528189

theorem tailTrace_1445793 : CollatzResearch.WordTrace tailWord_1445793 prefixEnd_1445793 329949660402652027528189 := by
  unfold tailWord_1445793
  simp only [CollatzResearch.WordTrace]
  refine ⟨52732402851146357631062033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35154935234097571754041355 52732402851146357631062033)
  ·
    refine ⟨39549302138359768223296525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52732402851146357631062033 39549302138359768223296525)
    ·
      refine ⟨14830988301884913083736197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39549302138359768223296525 14830988301884913083736197)
      ·
        refine ⟨2780810306603421203200537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14830988301884913083736197 2780810306603421203200537)
        ·
          refine ⟨2085607729952565902400403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2780810306603421203200537 2085607729952565902400403)
          ·
            refine ⟨3128411594928848853600605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085607729952565902400403 3128411594928848853600605)
            ·
              refine ⟨1173154348098318320100227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3128411594928848853600605 1173154348098318320100227)
              ·
                refine ⟨1759731522147477480150341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173154348098318320100227 1759731522147477480150341)
                ·
                  refine ⟨329949660402652027528189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1759731522147477480150341 329949660402652027528189)
                  ·
                    rfl

theorem cell21_1445793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_1445793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445793 prefixEnd_1445793 := by exact prefixLift 1445793
  have htrace : WordTrace (prefixWord ++ tailWord_1445793) baseStart_1445793 baseEnd_1445793 := by
    simpa [prefixWord, tailWord_1445793, baseEnd_1445793] using wordTrace_append hprefix tailTrace_1445793
  have hstable : (prefixWord ++ tailWord_1445793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445793).length < 2 ^ (prefixWord ++ tailWord_1445793).sum := by decide
  have hdescent : baseEnd_1445793 < baseStart_1445793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445838 : List Nat := [4, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_1445838 : Nat := 118140960795 + 1445838 * 2 ^ 59
def prefixEnd_1445838 : Nat := 4983230072969 + 3 ^ 40 * 1445838 * 2
def baseEnd_1445838 : Nat := 329959930015741949278097

theorem tailTrace_1445838 : CollatzResearch.WordTrace tailWord_1445838 prefixEnd_1445838 329959930015741949278097 := by
  unfold tailWord_1445838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6591755516997916289556271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35156029423988886877633445 6591755516997916289556271)
  ·
    refine ⟨9887633275496874434334407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6591755516997916289556271 9887633275496874434334407)
    ·
      refine ⟨14831449913245311651501611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9887633275496874434334407 14831449913245311651501611)
      ·
        refine ⟨22247174869867967477252417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14831449913245311651501611 22247174869867967477252417)
        ·
          refine ⟨16685381152400975607939313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22247174869867967477252417 16685381152400975607939313)
          ·
            refine ⟨12514035864300731705954485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16685381152400975607939313 12514035864300731705954485)
            ·
              refine ⟨1173190862278193597433233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12514035864300731705954485 1173190862278193597433233)
              ·
                refine ⟨879893146708645198074925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173190862278193597433233 879893146708645198074925)
                ·
                  refine ⟨329959930015741949278097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879893146708645198074925 329959930015741949278097)
                  ·
                    rfl

theorem cell21_1445838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_1445838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445838 prefixEnd_1445838 := by exact prefixLift 1445838
  have htrace : WordTrace (prefixWord ++ tailWord_1445838) baseStart_1445838 baseEnd_1445838 := by
    simpa [prefixWord, tailWord_1445838, baseEnd_1445838] using wordTrace_append hprefix tailTrace_1445838
  have hstable : (prefixWord ++ tailWord_1445838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445838).length < 2 ^ (prefixWord ++ tailWord_1445838).sum := by decide
  have hdescent : baseEnd_1445838 < baseStart_1445838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1445945 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 4]
def baseStart_1445945 : Nat := 118140960795 + 1445945 * 2 ^ 59
def prefixEnd_1445945 : Nat := 4983230072969 + 3 ^ 40 * 1445945 * 2
def baseEnd_1445945 : Nat := 329984348873533540994545

theorem tailTrace_1445945 : CollatzResearch.WordTrace tailWord_1445945 prefixEnd_1445945 329984348873533540994545 := by
  unfold tailWord_1445945
  simp only [CollatzResearch.WordTrace]
  refine ⟨52737946746595687590595289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35158631164397125060396859 52737946746595687590595289)
  ·
    refine ⟨39553460059946765692946467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52737946746595687590595289 39553460059946765692946467)
    ·
      refine ⟨59330190089920148539419701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39553460059946765692946467 59330190089920148539419701)
      ·
        refine ⟨5562205320930013925570597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59330190089920148539419701 5562205320930013925570597)
        ·
          refine ⟨1042913497674377611044487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5562205320930013925570597 1042913497674377611044487)
          ·
            refine ⟨1564370246511566416566731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042913497674377611044487 1564370246511566416566731)
            ·
              refine ⟨2346555369767349624850097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564370246511566416566731 2346555369767349624850097)
              ·
                refine ⟨1759916527325512218637573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2346555369767349624850097 1759916527325512218637573)
                ·
                  refine ⟨329984348873533540994545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1759916527325512218637573 329984348873533540994545)
                  ·
                    rfl

theorem cell21_1445945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 4].length) (baseStart_1445945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1445945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1445945 prefixEnd_1445945 := by exact prefixLift 1445945
  have htrace : WordTrace (prefixWord ++ tailWord_1445945) baseStart_1445945 baseEnd_1445945 := by
    simpa [prefixWord, tailWord_1445945, baseEnd_1445945] using wordTrace_append hprefix tailTrace_1445945
  have hstable : (prefixWord ++ tailWord_1445945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1445945).length < 2 ^ (prefixWord ++ tailWord_1445945).sum := by decide
  have hdescent : baseEnd_1445945 < baseStart_1445945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1445945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446091 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 5]
def baseStart_1446091 : Nat := 118140960795 + 1446091 * 2 ^ 59
def prefixEnd_1446091 : Nat := 4983230072969 + 3 ^ 40 * 1446091 * 2
def baseEnd_1446091 : Nat := 330017668062669731560913

theorem tailTrace_1446091 : CollatzResearch.WordTrace tailWord_1446091 prefixEnd_1446091 330017668062669731560913 := by
  unfold tailWord_1446091
  simp only [CollatzResearch.WordTrace]
  refine ⟨52743271804066754525410127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35162181202711169683606751 52743271804066754525410127)
  ·
    refine ⟨79114907706100131788115191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52743271804066754525410127 79114907706100131788115191)
    ·
      refine ⟨118672361559150197682172787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79114907706100131788115191 118672361559150197682172787)
      ·
        refine ⟨178008542338725296523259181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118672361559150197682172787 178008542338725296523259181)
        ·
          refine ⟨66753203377021986196222193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178008542338725296523259181 66753203377021986196222193)
          ·
            refine ⟨50064902532766489647166645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66753203377021986196222193 50064902532766489647166645)
            ·
              refine ⟨4693584612446858404421873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50064902532766489647166645 4693584612446858404421873)
              ·
                refine ⟨3520188459335143803316405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4693584612446858404421873 3520188459335143803316405)
                ·
                  refine ⟨330017668062669731560913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3520188459335143803316405 330017668062669731560913)
                  ·
                    rfl

theorem cell21_1446091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_1446091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446091 prefixEnd_1446091 := by exact prefixLift 1446091
  have htrace : WordTrace (prefixWord ++ tailWord_1446091) baseStart_1446091 baseEnd_1446091 := by
    simpa [prefixWord, tailWord_1446091, baseEnd_1446091] using wordTrace_append hprefix tailTrace_1446091
  have hstable : (prefixWord ++ tailWord_1446091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446091).length < 2 ^ (prefixWord ++ tailWord_1446091).sum := by decide
  have hdescent : baseEnd_1446091 < baseStart_1446091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446094 : List Nat := [4, 1, 1, 1, 4, 2, 3, 5]
def baseStart_1446094 : Nat := 118140960795 + 1446094 * 2 ^ 59
def prefixEnd_1446094 : Nat := 4983230072969 + 3 ^ 40 * 1446094 * 2
def baseEnd_1446094 : Nat := 110006117567847464336969

theorem tailTrace_1446094 : CollatzResearch.WordTrace tailWord_1446094 prefixEnd_1446094 110006117567847464336969 := by
  unfold tailWord_1446094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592922652881985754721167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35162254148703924025179557 6592922652881985754721167)
  ·
    refine ⟨9889383979322978632081751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6592922652881985754721167 9889383979322978632081751)
    ·
      refine ⟨14834075968984467948122627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9889383979322978632081751 14834075968984467948122627)
      ·
        refine ⟨22251113953476701922183941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14834075968984467948122627 22251113953476701922183941)
        ·
          refine ⟨4172083866276881610409489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22251113953476701922183941 4172083866276881610409489)
          ·
            refine ⟨3129062899707661207807117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4172083866276881610409489 3129062899707661207807117)
            ·
              refine ⟨1173398587390372952927669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3129062899707661207807117 1173398587390372952927669)
              ·
                refine ⟨110006117567847464336969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1173398587390372952927669 110006117567847464336969)
                ·
                  rfl

theorem cell21_1446094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_1446094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446094 prefixEnd_1446094 := by exact prefixLift 1446094
  have htrace : WordTrace (prefixWord ++ tailWord_1446094) baseStart_1446094 baseEnd_1446094 := by
    simpa [prefixWord, tailWord_1446094, baseEnd_1446094] using wordTrace_append hprefix tailTrace_1446094
  have hstable : (prefixWord ++ tailWord_1446094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446094).length < 2 ^ (prefixWord ++ tailWord_1446094).sum := by decide
  have hdescent : baseEnd_1446094 < baseStart_1446094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446122 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_1446122 : Nat := 118140960795 + 1446122 * 2 ^ 59
def prefixEnd_1446122 : Nat := 4983230072969 + 3 ^ 40 * 1446122 * 2
def baseEnd_1446122 : Nat := 330024742685020566544183

theorem tailTrace_1446122 : CollatzResearch.WordTrace tailWord_1446122 prefixEnd_1446122 330024742685020566544183 := by
  unfold tailWord_1446122
  simp only [CollatzResearch.WordTrace]
  refine ⟨13186100616738611704947155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35162934977969631213192413 13186100616738611704947155)
  ·
    refine ⟨19779150925107917557420733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13186100616738611704947155 19779150925107917557420733)
    ·
      refine ⟨7417181596915469084032775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19779150925107917557420733 7417181596915469084032775)
      ·
        refine ⟨11125772395373203626049163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7417181596915469084032775 11125772395373203626049163)
        ·
          refine ⟨16688658593059805439073745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11125772395373203626049163 16688658593059805439073745)
          ·
            refine ⟨12516493944794854079305309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16688658593059805439073745 12516493944794854079305309)
            ·
              refine ⟨4693685229298070279739491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12516493944794854079305309 4693685229298070279739491)
              ·
                refine ⟨7040527843947105419609237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4693685229298070279739491 7040527843947105419609237)
                ·
                  refine ⟨330024742685020566544183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7040527843947105419609237 330024742685020566544183)
                  ·
                    rfl

theorem cell21_1446122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_1446122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446122 prefixEnd_1446122 := by exact prefixLift 1446122
  have htrace : WordTrace (prefixWord ++ tailWord_1446122) baseStart_1446122 baseEnd_1446122 := by
    simpa [prefixWord, tailWord_1446122, baseEnd_1446122] using wordTrace_append hprefix tailTrace_1446122
  have hstable : (prefixWord ++ tailWord_1446122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446122).length < 2 ^ (prefixWord ++ tailWord_1446122).sum := by decide
  have hdescent : baseEnd_1446122 < baseStart_1446122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446125 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1446125 : Nat := 118140960795 + 1446125 * 2 ^ 59
def prefixEnd_1446125 : Nat := 4983230072969 + 3 ^ 40 * 1446125 * 2
def baseEnd_1446125 : Nat := 330025427325893227994177

theorem tailTrace_1446125 : CollatzResearch.WordTrace tailWord_1446125 prefixEnd_1446125 330025427325893227994177 := by
  unfold tailWord_1446125
  simp only [CollatzResearch.WordTrace]
  refine ⟨52744511885943578332147829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35163007923962385554765219 52744511885943578332147829)
  ·
    refine ⟨4944797989307210468638859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52744511885943578332147829 4944797989307210468638859)
    ·
      refine ⟨7417196983960815702958289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4944797989307210468638859 7417196983960815702958289)
      ·
        refine ⟨5562897737970611777218717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7417196983960815702958289 5562897737970611777218717)
        ·
          refine ⟨2086086651738979416457019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5562897737970611777218717 2086086651738979416457019)
          ·
            refine ⟨3129129977608469124685529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086086651738979416457019 3129129977608469124685529)
            ·
              refine ⟨2346847483206351843514147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3129129977608469124685529 2346847483206351843514147)
              ·
                refine ⟨3520271224809527765271221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2346847483206351843514147 3520271224809527765271221)
                ·
                  refine ⟨330025427325893227994177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3520271224809527765271221 330025427325893227994177)
                  ·
                    rfl

theorem cell21_1446125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1446125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446125 prefixEnd_1446125 := by exact prefixLift 1446125
  have htrace : WordTrace (prefixWord ++ tailWord_1446125) baseStart_1446125 baseEnd_1446125 := by
    simpa [prefixWord, tailWord_1446125, baseEnd_1446125] using wordTrace_append hprefix tailTrace_1446125
  have hstable : (prefixWord ++ tailWord_1446125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446125).length < 2 ^ (prefixWord ++ tailWord_1446125).sum := by decide
  have hdescent : baseEnd_1446125 < baseStart_1446125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446153 : List Nat := [1, 2, 1, 1, 3, 4, 4, 5]
def baseStart_1446153 : Nat := 118140960795 + 1446153 * 2 ^ 59
def prefixEnd_1446153 : Nat := 4983230072969 + 3 ^ 40 * 1446153 * 2
def baseEnd_1446153 : Nat := 110010605769123800509151

theorem tailTrace_1446153 : CollatzResearch.WordTrace tailWord_1446153 prefixEnd_1446153 110010605769123800509151 := by
  unfold tailWord_1446153
  simp only [CollatzResearch.WordTrace]
  refine ⟨52745533129842139114167113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35163688753228092742778075 52745533129842139114167113)
  ·
    refine ⟨39559149847381604335625335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52745533129842139114167113 39559149847381604335625335)
    ·
      refine ⟨59338724771072406503438003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39559149847381604335625335 59338724771072406503438003)
      ·
        refine ⟨89008087156608609755157005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59338724771072406503438003 89008087156608609755157005)
        ·
          refine ⟨33378032683728228658183877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89008087156608609755157005 33378032683728228658183877)
          ·
            refine ⟨6258381128199042873409477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33378032683728228658183877 6258381128199042873409477)
            ·
              refine ⟨1173446461537320538764277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6258381128199042873409477 1173446461537320538764277)
              ·
                refine ⟨110010605769123800509151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1173446461537320538764277 110010605769123800509151)
                ·
                  rfl

theorem cell21_1446153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 5].length) (baseStart_1446153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446153 prefixEnd_1446153 := by exact prefixLift 1446153
  have htrace : WordTrace (prefixWord ++ tailWord_1446153) baseStart_1446153 baseEnd_1446153 := by
    simpa [prefixWord, tailWord_1446153, baseEnd_1446153] using wordTrace_append hprefix tailTrace_1446153
  have hstable : (prefixWord ++ tailWord_1446153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446153).length < 2 ^ (prefixWord ++ tailWord_1446153).sum := by decide
  have hdescent : baseEnd_1446153 < baseStart_1446153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446170 : List Nat := [3, 1, 1, 3, 5, 1, 7]
def baseStart_1446170 : Nat := 118140960795 + 1446170 * 2 ^ 59
def prefixEnd_1446170 : Nat := 4983230072969 + 3 ^ 40 * 1446170 * 2
def baseEnd_1446170 : Nat := 36670632993220349971565

theorem tailTrace_1446170 : CollatzResearch.WordTrace tailWord_1446170 prefixEnd_1446170 36670632993220349971565 := by
  unfold tailWord_1446170
  simp only [CollatzResearch.WordTrace]
  refine ⟨13186538292695137754383991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35164102113853700678357309 13186538292695137754383991)
  ·
    refine ⟨19779807439042706631575987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13186538292695137754383991 19779807439042706631575987)
    ·
      refine ⟨29669711158564059947363981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19779807439042706631575987 29669711158564059947363981)
      ·
        refine ⟨11126141684461522480261493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29669711158564059947363981 11126141684461522480261493)
        ·
          refine ⟨1043075782918267732524515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11126141684461522480261493 1043075782918267732524515)
          ·
            refine ⟨1564613674377401598786773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043075782918267732524515 1564613674377401598786773)
            ·
              refine ⟨36670632993220349971565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1564613674377401598786773 36670632993220349971565)
              ·
                rfl

theorem cell21_1446170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 7].length) (baseStart_1446170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446170 prefixEnd_1446170 := by exact prefixLift 1446170
  have htrace : WordTrace (prefixWord ++ tailWord_1446170) baseStart_1446170 baseEnd_1446170 := by
    simpa [prefixWord, tailWord_1446170, baseEnd_1446170] using wordTrace_append hprefix tailTrace_1446170
  have hstable : (prefixWord ++ tailWord_1446170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446170).length < 2 ^ (prefixWord ++ tailWord_1446170).sum := by decide
  have hdescent : baseEnd_1446170 < baseStart_1446170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446190 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_1446190 : Nat := 118140960795 + 1446190 * 2 ^ 59
def prefixEnd_1446190 : Nat := 4983230072969 + 3 ^ 40 * 1446190 * 2
def baseEnd_1446190 : Nat := 330040261211467559410711

theorem tailTrace_1446190 : CollatzResearch.WordTrace tailWord_1446190 prefixEnd_1446190 330040261211467559410711 := by
  unfold tailWord_1446190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6593360328838511804158003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35164588420472062955509349 6593360328838511804158003)
  ·
    refine ⟨9890040493257767706237005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6593360328838511804158003 9890040493257767706237005)
    ·
      refine ⟨3708765184971662889838877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9890040493257767706237005 3708765184971662889838877)
      ·
        refine ⟨1390786944364373583689579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3708765184971662889838877 1390786944364373583689579)
        ·
          refine ⟨2086180416546560375534369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390786944364373583689579 2086180416546560375534369)
          ·
            refine ⟨1564635312409920281650777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2086180416546560375534369 1564635312409920281650777)
            ·
              refine ⟨1173476484307440211238083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1564635312409920281650777 1173476484307440211238083)
              ·
                refine ⟨1760214726461160316857125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173476484307440211238083 1760214726461160316857125)
                ·
                  refine ⟨330040261211467559410711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1760214726461160316857125 330040261211467559410711)
                  ·
                    rfl

theorem cell21_1446190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_1446190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446190 prefixEnd_1446190 := by exact prefixLift 1446190
  have htrace : WordTrace (prefixWord ++ tailWord_1446190) baseStart_1446190 baseEnd_1446190 := by
    simpa [prefixWord, tailWord_1446190, baseEnd_1446190] using wordTrace_append hprefix tailTrace_1446190
  have hstable : (prefixWord ++ tailWord_1446190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446190).length < 2 ^ (prefixWord ++ tailWord_1446190).sum := by decide
  have hdescent : baseEnd_1446190 < baseStart_1446190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446229 : List Nat := [1, 3, 2, 2, 5, 8]
def baseStart_1446229 : Nat := 118140960795 + 1446229 * 2 ^ 59
def prefixEnd_1446229 : Nat := 4983230072969 + 3 ^ 40 * 1446229 * 2
def baseEnd_1446229 : Nat := 12224043020104154009653

theorem tailTrace_1446229 : CollatzResearch.WordTrace tailWord_1446229 prefixEnd_1446229 12224043020104154009653 := by
  unfold tailWord_1446229
  simp only [CollatzResearch.WordTrace]
  refine ⟨52748305077566804093933741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35165536718377869395955827 52748305077566804093933741)
  ·
    refine ⟨19780614404087551535225153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52748305077566804093933741 19780614404087551535225153)
    ·
      refine ⟨14835460803065663651418865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19780614404087551535225153 14835460803065663651418865)
      ·
        refine ⟨11126595602299247738564149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14835460803065663651418865 11126595602299247738564149)
        ·
          refine ⟨1043118337715554475490389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11126595602299247738564149 1043118337715554475490389)
          ·
            refine ⟨12224043020104154009653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1043118337715554475490389 12224043020104154009653)
            ·
              rfl

theorem cell21_1446229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 8].length) (baseStart_1446229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446229 prefixEnd_1446229 := by exact prefixLift 1446229
  have htrace : WordTrace (prefixWord ++ tailWord_1446229) baseStart_1446229 baseEnd_1446229 := by
    simpa [prefixWord, tailWord_1446229, baseEnd_1446229] using wordTrace_append hprefix tailTrace_1446229
  have hstable : (prefixWord ++ tailWord_1446229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446229).length < 2 ^ (prefixWord ++ tailWord_1446229).sum := by decide
  have hdescent : baseEnd_1446229 < baseStart_1446229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446238 : List Nat := [4, 4, 2, 1, 2, 1, 1, 6]
def baseStart_1446238 : Nat := 118140960795 + 1446238 * 2 ^ 59
def prefixEnd_1446238 : Nat := 4983230072969 + 3 ^ 40 * 1446238 * 2
def baseEnd_1446238 : Nat := 110017071821810047536871

theorem tailTrace_1446238 : CollatzResearch.WordTrace tailWord_1446238 prefixEnd_1446238 110017071821810047536871 := by
  unfold tailWord_1446238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6593579166816774828876421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35165755556356132420674245 6593579166816774828876421)
  ·
    refine ⟨1236296093778145280414329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6593579166816774828876421 1236296093778145280414329)
    ·
      refine ⟨927222070333608960310747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1236296093778145280414329 927222070333608960310747)
      ·
        refine ⟨1390833105500413440466121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927222070333608960310747 1390833105500413440466121)
        ·
          refine ⟨1043124829125310080349591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1390833105500413440466121 1043124829125310080349591)
          ·
            refine ⟨1564687243687965120524387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043124829125310080349591 1564687243687965120524387)
            ·
              refine ⟨2347030865531947680786581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564687243687965120524387 2347030865531947680786581)
              ·
                refine ⟨110017071821810047536871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2347030865531947680786581 110017071821810047536871)
                ·
                  rfl

theorem cell21_1446238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_1446238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446238 prefixEnd_1446238 := by exact prefixLift 1446238
  have htrace : WordTrace (prefixWord ++ tailWord_1446238) baseStart_1446238 baseEnd_1446238 := by
    simpa [prefixWord, tailWord_1446238, baseEnd_1446238] using wordTrace_append hprefix tailTrace_1446238
  have hstable : (prefixWord ++ tailWord_1446238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446238).length < 2 ^ (prefixWord ++ tailWord_1446238).sum := by decide
  have hdescent : baseEnd_1446238 < baseStart_1446238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446243 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 5]
def baseStart_1446243 : Nat := 118140960795 + 1446243 * 2 ^ 59
def prefixEnd_1446243 : Nat := 4983230072969 + 3 ^ 40 * 1446243 * 2
def baseEnd_1446243 : Nat := 330052356533551245027269

theorem tailTrace_1446243 : CollatzResearch.WordTrace tailWord_1446243 prefixEnd_1446243 330052356533551245027269 := by
  unfold tailWord_1446243
  simp only [CollatzResearch.WordTrace]
  refine ⟨52748815699516084484943383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35165877133010722989962255 52748815699516084484943383)
  ·
    refine ⟨79123223549274126727415075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52748815699516084484943383 79123223549274126727415075)
    ·
      refine ⟨118684835323911190091122613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79123223549274126727415075 118684835323911190091122613)
      ·
        refine ⟨11126703311616674071042745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118684835323911190091122613 11126703311616674071042745)
        ·
          refine ⟨8345027483712505553282059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11126703311616674071042745 8345027483712505553282059)
          ·
            refine ⟨12517541225568758329923089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8345027483712505553282059 12517541225568758329923089)
            ·
              refine ⟨9388155919176568747442317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12517541225568758329923089 9388155919176568747442317)
              ·
                refine ⟨3520558469691213280290869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9388155919176568747442317 3520558469691213280290869)
                ·
                  refine ⟨330052356533551245027269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3520558469691213280290869 330052356533551245027269)
                  ·
                    rfl

theorem cell21_1446243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_1446243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446243 prefixEnd_1446243 := by exact prefixLift 1446243
  have htrace : WordTrace (prefixWord ++ tailWord_1446243) baseStart_1446243 baseEnd_1446243 := by
    simpa [prefixWord, tailWord_1446243, baseEnd_1446243] using wordTrace_append hprefix tailTrace_1446243
  have hstable : (prefixWord ++ tailWord_1446243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446243).length < 2 ^ (prefixWord ++ tailWord_1446243).sum := by decide
  have hdescent : baseEnd_1446243 < baseStart_1446243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446257 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 8]
def baseStart_1446257 : Nat := 118140960795 + 1446257 * 2 ^ 59
def prefixEnd_1446257 : Nat := 4983230072969 + 3 ^ 40 * 1446257 * 2
def baseEnd_1446257 : Nat := 330055551524290331793907

theorem tailTrace_1446257 : CollatzResearch.WordTrace tailWord_1446257 prefixEnd_1446257 330055551524290331793907 := by
  unfold tailWord_1446257
  simp only [CollatzResearch.WordTrace]
  refine ⟨52749326321465364875953025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35166217547643576583968683 52749326321465364875953025)
  ·
    refine ⟨39561994741099023656964769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52749326321465364875953025 39561994741099023656964769)
    ·
      refine ⟨29671496055824267742723577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39561994741099023656964769 29671496055824267742723577)
      ·
        refine ⟨22253622041868200807042683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29671496055824267742723577 22253622041868200807042683)
        ·
          refine ⟨33380433062802301210564025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22253622041868200807042683 33380433062802301210564025)
          ·
            refine ⟨25035324797101725907923019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33380433062802301210564025 25035324797101725907923019)
            ·
              refine ⟨37552987195652588861884529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25035324797101725907923019 37552987195652588861884529)
              ·
                refine ⟨28164740396739441646413397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37552987195652588861884529 28164740396739441646413397)
                ·
                  refine ⟨330055551524290331793907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28164740396739441646413397 330055551524290331793907)
                  ·
                    rfl

theorem cell21_1446257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_1446257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446257 prefixEnd_1446257 := by exact prefixLift 1446257
  have htrace : WordTrace (prefixWord ++ tailWord_1446257) baseStart_1446257 baseEnd_1446257 := by
    simpa [prefixWord, tailWord_1446257, baseEnd_1446257] using wordTrace_append hprefix tailTrace_1446257
  have hstable : (prefixWord ++ tailWord_1446257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446257).length < 2 ^ (prefixWord ++ tailWord_1446257).sum := by decide
  have hdescent : baseEnd_1446257 < baseStart_1446257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446350 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_1446350 : Nat := 118140960795 + 1446350 * 2 ^ 59
def prefixEnd_1446350 : Nat := 4983230072969 + 3 ^ 40 * 1446350 * 2
def baseEnd_1446350 : Nat := 330076775391342836743717

theorem tailTrace_1446350 : CollatzResearch.WordTrace tailWord_1446350 prefixEnd_1446350 330076775391342836743717 := by
  unfold tailWord_1446350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6594089788766055219886063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35168478873418961172725669 6594089788766055219886063)
  ·
    refine ⟨9891134683149082829829095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6594089788766055219886063 9891134683149082829829095)
    ·
      refine ⟨14836702024723624244743643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9891134683149082829829095 14836702024723624244743643)
      ·
        refine ⟨22255053037085436367115465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14836702024723624244743643 22255053037085436367115465)
        ·
          refine ⟨16691289777814077275336599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22255053037085436367115465 16691289777814077275336599)
          ·
            refine ⟨25036934666721115913004899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16691289777814077275336599 25036934666721115913004899)
            ·
              refine ⟨37555402000081673869507349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25036934666721115913004899 37555402000081673869507349)
              ·
                refine ⟨1760409468753828462633157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37555402000081673869507349 1760409468753828462633157)
                ·
                  refine ⟨330076775391342836743717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1760409468753828462633157 330076775391342836743717)
                  ·
                    rfl

theorem cell21_1446350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_1446350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446350 prefixEnd_1446350 := by exact prefixLift 1446350
  have htrace : WordTrace (prefixWord ++ tailWord_1446350) baseStart_1446350 baseEnd_1446350 := by
    simpa [prefixWord, tailWord_1446350, baseEnd_1446350] using wordTrace_append hprefix tailTrace_1446350
  have hstable : (prefixWord ++ tailWord_1446350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446350).length < 2 ^ (prefixWord ++ tailWord_1446350).sum := by decide
  have hdescent : baseEnd_1446350 < baseStart_1446350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446367 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 4]
def baseStart_1446367 : Nat := 118140960795 + 1446367 * 2 ^ 59
def prefixEnd_1446367 : Nat := 4983230072969 + 3 ^ 40 * 1446367 * 2
def baseEnd_1446367 : Nat := 330080655022954584960349

theorem tailTrace_1446367 : CollatzResearch.WordTrace tailWord_1446367 prefixEnd_1446367 330080655022954584960349 := by
  unfold tailWord_1446367
  simp only [CollatzResearch.WordTrace]
  refine ⟨52753338351066853662457355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35168892234044569108304903 52753338351066853662457355)
  ·
    refine ⟨79130007526600280493686033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52753338351066853662457355 79130007526600280493686033)
    ·
      refine ⟨59347505644950210370264525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79130007526600280493686033 59347505644950210370264525)
      ·
        refine ⟨22255314616856328888849197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59347505644950210370264525 22255314616856328888849197)
        ·
          refine ⟨8345742981321123333318449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22255314616856328888849197 8345742981321123333318449)
          ·
            refine ⟨6259307235990842499988837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8345742981321123333318449 6259307235990842499988837)
            ·
              refine ⟨1173620106748282968747907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6259307235990842499988837 1173620106748282968747907)
              ·
                refine ⟨1760430160122424453121861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173620106748282968747907 1760430160122424453121861)
                ·
                  refine ⟨330080655022954584960349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1760430160122424453121861 330080655022954584960349)
                  ·
                    rfl

theorem cell21_1446367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 4].length) (baseStart_1446367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446367 prefixEnd_1446367 := by exact prefixLift 1446367
  have htrace : WordTrace (prefixWord ++ tailWord_1446367) baseStart_1446367 baseEnd_1446367 := by
    simpa [prefixWord, tailWord_1446367, baseEnd_1446367] using wordTrace_append hprefix tailTrace_1446367
  have hstable : (prefixWord ++ tailWord_1446367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446367).length < 2 ^ (prefixWord ++ tailWord_1446367).sum := by decide
  have hdescent : baseEnd_1446367 < baseStart_1446367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446381 : List Nat := [1, 5, 1, 3, 1, 1, 2, 7]
def baseStart_1446381 : Nat := 118140960795 + 1446381 * 2 ^ 59
def prefixEnd_1446381 : Nat := 4983230072969 + 3 ^ 40 * 1446381 * 2
def baseEnd_1446381 : Nat := 110027950004564557242329

theorem tailTrace_1446381 : CollatzResearch.WordTrace tailWord_1446381 prefixEnd_1446381 110027950004564557242329 := by
  unfold tailWord_1446381
  simp only [CollatzResearch.WordTrace]
  refine ⟨52753848973016134053466997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35169232648677422702311331 52753848973016134053466997)
  ·
    refine ⟨4945673341220262567512531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52753848973016134053466997 4945673341220262567512531)
    ·
      refine ⟨7418510011830393851268797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4945673341220262567512531 7418510011830393851268797)
      ·
        refine ⟨2781941254436397694225799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7418510011830393851268797 2781941254436397694225799)
        ·
          refine ⟨4172911881654596541338699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781941254436397694225799 4172911881654596541338699)
          ·
            refine ⟨6259367822481894812008049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172911881654596541338699 6259367822481894812008049)
            ·
              refine ⟨4694525866861421109006037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6259367822481894812008049 4694525866861421109006037)
              ·
                refine ⟨110027950004564557242329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4694525866861421109006037 110027950004564557242329)
                ·
                  rfl

theorem cell21_1446381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 7].length) (baseStart_1446381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446381 prefixEnd_1446381 := by exact prefixLift 1446381
  have htrace : WordTrace (prefixWord ++ tailWord_1446381) baseStart_1446381 baseEnd_1446381 := by
    simpa [prefixWord, tailWord_1446381, baseEnd_1446381] using wordTrace_append hprefix tailTrace_1446381
  have hstable : (prefixWord ++ tailWord_1446381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446381).length < 2 ^ (prefixWord ++ tailWord_1446381).sum := by decide
  have hdescent : baseEnd_1446381 < baseStart_1446381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446426 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_1446426 : Nat := 118140960795 + 1446426 * 2 ^ 59
def prefixEnd_1446426 : Nat := 4983230072969 + 3 ^ 40 * 1446426 * 2
def baseEnd_1446426 : Nat := 330094119626783593476895

theorem tailTrace_1446426 : CollatzResearch.WordTrace tailWord_1446426 prefixEnd_1446426 330094119626783593476895 := by
  unfold tailWord_1446426
  simp only [CollatzResearch.WordTrace]
  refine ⟨13188872564463276684713783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35170326838568737825903421 13188872564463276684713783)
  ·
    refine ⟨19783308846694915027070675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13188872564463276684713783 19783308846694915027070675)
    ·
      refine ⟨29674963270042372540606013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19783308846694915027070675 29674963270042372540606013)
      ·
        refine ⟨11128111226265889702727255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29674963270042372540606013 11128111226265889702727255)
        ·
          refine ⟨16692166839398834554090883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11128111226265889702727255 16692166839398834554090883)
          ·
            refine ⟨25038250259098251831136325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16692166839398834554090883 25038250259098251831136325)
            ·
              refine ⟨4694671923580922218338061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25038250259098251831136325 4694671923580922218338061)
              ·
                refine ⟨1760501971342845831876773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4694671923580922218338061 1760501971342845831876773)
                ·
                  refine ⟨330094119626783593476895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1760501971342845831876773 330094119626783593476895)
                  ·
                    rfl

theorem cell21_1446426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_1446426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446426 prefixEnd_1446426 := by exact prefixLift 1446426
  have htrace : WordTrace (prefixWord ++ tailWord_1446426) baseStart_1446426 baseEnd_1446426 := by
    simpa [prefixWord, tailWord_1446426, baseEnd_1446426] using wordTrace_append hprefix tailTrace_1446426
  have hstable : (prefixWord ++ tailWord_1446426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446426).length < 2 ^ (prefixWord ++ tailWord_1446426).sum := by decide
  have hdescent : baseEnd_1446426 < baseStart_1446426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446446 : List Nat := [4, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_1446446 : Nat := 118140960795 + 1446446 * 2 ^ 59
def prefixEnd_1446446 : Nat := 4983230072969 + 3 ^ 40 * 1446446 * 2
def baseEnd_1446446 : Nat := 330098683899268003143521

theorem tailTrace_1446446 : CollatzResearch.WordTrace tailWord_1446446 prefixEnd_1446446 330098683899268003143521 := by
  unfold tailWord_1446446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6594527464722581269322899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35170813145187100103055461 6594527464722581269322899)
  ·
    refine ⟨9891791197083871903984349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6594527464722581269322899 9891791197083871903984349)
    ·
      refine ⟨3709421698906451963994131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9891791197083871903984349 3709421698906451963994131)
      ·
        refine ⟨5564132548359677945991197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3709421698906451963994131 5564132548359677945991197)
        ·
          refine ⟨2086549705634879229746699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5564132548359677945991197 2086549705634879229746699)
          ·
            refine ⟨3129824558452318844620049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086549705634879229746699 3129824558452318844620049)
            ·
              refine ⟨2347368418839239133465037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3129824558452318844620049 2347368418839239133465037)
              ·
                refine ⟨880263157064714675049389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2347368418839239133465037 880263157064714675049389)
                ·
                  refine ⟨330098683899268003143521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880263157064714675049389 330098683899268003143521)
                  ·
                    rfl

theorem cell21_1446446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_1446446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446446 prefixEnd_1446446 := by exact prefixLift 1446446
  have htrace : WordTrace (prefixWord ++ tailWord_1446446) baseStart_1446446 baseEnd_1446446 := by
    simpa [prefixWord, tailWord_1446446, baseEnd_1446446] using wordTrace_append hprefix tailTrace_1446446
  have hstable : (prefixWord ++ tailWord_1446446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446446).length < 2 ^ (prefixWord ++ tailWord_1446446).sum := by decide
  have hdescent : baseEnd_1446446 < baseStart_1446446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446471 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 5]
def baseStart_1446471 : Nat := 118140960795 + 1446471 * 2 ^ 59
def prefixEnd_1446471 : Nat := 4983230072969 + 3 ^ 40 * 1446471 * 2
def baseEnd_1446471 : Nat := 330104389239873515226803

theorem tailTrace_1446471 : CollatzResearch.WordTrace tailWord_1446471 prefixEnd_1446471 330104389239873515226803 := by
  unfold tailWord_1446471
  simp only [CollatzResearch.WordTrace]
  refine ⟨52757131542690079424243267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35171421028460052949495511 52757131542690079424243267)
  ·
    refine ⟨79135697314035119136364901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52757131542690079424243267 79135697314035119136364901)
    ·
      refine ⟨14837943246381584838068419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79135697314035119136364901 14837943246381584838068419)
      ·
        refine ⟨22256914869572377257102629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14837943246381584838068419 22256914869572377257102629)
        ·
          refine ⟨4173171538044820735706743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22256914869572377257102629 4173171538044820735706743)
          ·
            refine ⟨6259757307067231103560115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173171538044820735706743 6259757307067231103560115)
            ·
              refine ⟨9389635960600846655340173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6259757307067231103560115 9389635960600846655340173)
              ·
                refine ⟨3521113485225317495752565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9389635960600846655340173 3521113485225317495752565)
                ·
                  refine ⟨330104389239873515226803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3521113485225317495752565 330104389239873515226803)
                  ·
                    rfl

theorem cell21_1446471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_1446471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446471 prefixEnd_1446471 := by exact prefixLift 1446471
  have htrace : WordTrace (prefixWord ++ tailWord_1446471) baseStart_1446471 baseEnd_1446471 := by
    simpa [prefixWord, tailWord_1446471, baseEnd_1446471] using wordTrace_append hprefix tailTrace_1446471
  have hstable : (prefixWord ++ tailWord_1446471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446471).length < 2 ^ (prefixWord ++ tailWord_1446471).sum := by decide
  have hdescent : baseEnd_1446471 < baseStart_1446471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446564 : List Nat := [2, 3, 1, 2, 2, 1, 2, 5, 3]
def baseStart_1446564 : Nat := 118140960795 + 1446564 * 2 ^ 59
def prefixEnd_1446564 : Nat := 4983230072969 + 3 ^ 40 * 1446564 * 2
def baseEnd_1446564 : Nat := 330125613106926020176613

theorem tailTrace_1446564 : CollatzResearch.WordTrace tailWord_1446564 prefixEnd_1446564 330125613106926020176613 := by
  unfold tailWord_1446564
  simp only [CollatzResearch.WordTrace]
  refine ⟨26380261765676578153689373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35173682354235437538252497 26380261765676578153689373)
  ·
    refine ⟨9892598162128716807633515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26380261765676578153689373 9892598162128716807633515)
    ·
      refine ⟨14838897243193075211450273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9892598162128716807633515 14838897243193075211450273)
      ·
        refine ⟨11129172932394806408587705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14838897243193075211450273 11129172932394806408587705)
        ·
          refine ⟨8346879699296104806440779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11129172932394806408587705 8346879699296104806440779)
          ·
            refine ⟨12520319548944157209661169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8346879699296104806440779 12520319548944157209661169)
            ·
              refine ⟨9390239661708117907245877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12520319548944157209661169 9390239661708117907245877)
              ·
                refine ⟨880334968285136053804301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9390239661708117907245877 880334968285136053804301)
                ·
                  refine ⟨330125613106926020176613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880334968285136053804301 330125613106926020176613)
                  ·
                    rfl

theorem cell21_1446564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_1446564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446564 prefixEnd_1446564 := by exact prefixLift 1446564
  have htrace : WordTrace (prefixWord ++ tailWord_1446564) baseStart_1446564 baseEnd_1446564 := by
    simpa [prefixWord, tailWord_1446564, baseEnd_1446564] using wordTrace_append hprefix tailTrace_1446564
  have hstable : (prefixWord ++ tailWord_1446564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446564).length < 2 ^ (prefixWord ++ tailWord_1446564).sum := by decide
  have hdescent : baseEnd_1446564 < baseStart_1446564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446575 : List Nat := [1, 1, 2, 1, 2, 14]
def baseStart_1446575 : Nat := 118140960795 + 1446575 * 2 ^ 59
def prefixEnd_1446575 : Nat := 4983230072969 + 3 ^ 40 * 1446575 * 2
def baseEnd_1446575 : Nat := 12226967535436757240491

theorem tailTrace_1446575 : CollatzResearch.WordTrace tailWord_1446575 prefixEnd_1446575 12226967535436757240491 := by
  unfold tailWord_1446575
  simp only [CollatzResearch.WordTrace]
  refine ⟨52760924734313305186029179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35173949822875536790686119 52760924734313305186029179)
  ·
    refine ⟨79141387101469957779043769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52760924734313305186029179 79141387101469957779043769)
    ·
      refine ⟨59356040326102468334282827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79141387101469957779043769 59356040326102468334282827)
      ·
        refine ⟨89034060489153702501424241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59356040326102468334282827 89034060489153702501424241)
        ·
          refine ⟨66775545366865276876068181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89034060489153702501424241 66775545366865276876068181)
          ·
            refine ⟨12226967535436757240491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 66775545366865276876068181 12226967535436757240491)
            ·
              rfl

theorem cell21_1446575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 14].length) (baseStart_1446575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446575 prefixEnd_1446575 := by exact prefixLift 1446575
  have htrace : WordTrace (prefixWord ++ tailWord_1446575) baseStart_1446575 baseEnd_1446575 := by
    simpa [prefixWord, tailWord_1446575, baseEnd_1446575] using wordTrace_append hprefix tailTrace_1446575
  have hstable : (prefixWord ++ tailWord_1446575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446575).length < 2 ^ (prefixWord ++ tailWord_1446575).sum := by decide
  have hdescent : baseEnd_1446575 < baseStart_1446575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446581 : List Nat := [1, 3, 3, 3, 1, 2, 1, 4, 3]
def baseStart_1446581 : Nat := 118140960795 + 1446581 * 2 ^ 59
def prefixEnd_1446581 : Nat := 4983230072969 + 3 ^ 40 * 1446581 * 2
def baseEnd_1446581 : Nat := 330129492738537768393245

theorem tailTrace_1446581 : CollatzResearch.WordTrace tailWord_1446581 prefixEnd_1446581 330129492738537768393245 := by
  unfold tailWord_1446581
  simp only [CollatzResearch.WordTrace]
  refine ⟨52761143572291568210747597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35174095714861045473831731 52761143572291568210747597)
  ·
    refine ⟨19785428839609338079030349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52761143572291568210747597 19785428839609338079030349)
    ·
      refine ⟨7419535814853501779636381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19785428839609338079030349 7419535814853501779636381)
      ·
        refine ⟨2782325930570063167363643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7419535814853501779636381 2782325930570063167363643)
        ·
          refine ⟨4173488895855094751045465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782325930570063167363643 4173488895855094751045465)
          ·
            refine ⟨3130116671891321063284099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4173488895855094751045465 3130116671891321063284099)
            ·
              refine ⟨4695175007836981594926149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130116671891321063284099 4695175007836981594926149)
              ·
                refine ⟨880345313969434049048653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4695175007836981594926149 880345313969434049048653)
                ·
                  refine ⟨330129492738537768393245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880345313969434049048653 330129492738537768393245)
                  ·
                    rfl

theorem cell21_1446581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_1446581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446581 prefixEnd_1446581 := by exact prefixLift 1446581
  have htrace : WordTrace (prefixWord ++ tailWord_1446581) baseStart_1446581 baseEnd_1446581 := by
    simpa [prefixWord, tailWord_1446581, baseEnd_1446581] using wordTrace_append hprefix tailTrace_1446581
  have hstable : (prefixWord ++ tailWord_1446581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446581).length < 2 ^ (prefixWord ++ tailWord_1446581).sum := by decide
  have hdescent : baseEnd_1446581 < baseStart_1446581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446592 : List Nat := [2, 1, 1, 2, 4, 2, 3, 6]
def baseStart_1446592 : Nat := 118140960795 + 1446592 * 2 ^ 59
def prefixEnd_1446592 : Nat := 4983230072969 + 3 ^ 40 * 1446592 * 2
def baseEnd_1446592 : Nat := 110044001029468064569963

theorem tailTrace_1446592 : CollatzResearch.WordTrace tailWord_1446592 prefixEnd_1446592 110044001029468064569963 := by
  unfold tailWord_1446592
  simp only [CollatzResearch.WordTrace]
  refine ⟨26380772387625858544699015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35174363183501144726265353 26380772387625858544699015)
  ·
    refine ⟨39571158581438787817048523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26380772387625858544699015 39571158581438787817048523)
    ·
      refine ⟨59356737872158181725572785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39571158581438787817048523 59356737872158181725572785)
      ·
        refine ⟨44517553404118636294179589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59356737872158181725572785 44517553404118636294179589)
        ·
          refine ⟨8347041263272244305158673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44517553404118636294179589 8347041263272244305158673)
          ·
            refine ⟨6260280947454183228869005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8347041263272244305158673 6260280947454183228869005)
            ·
              refine ⟨2347605355295318710825877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6260280947454183228869005 2347605355295318710825877)
              ·
                refine ⟨110044001029468064569963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2347605355295318710825877 110044001029468064569963)
                ·
                  rfl

theorem cell21_1446592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_1446592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446592 prefixEnd_1446592 := by exact prefixLift 1446592
  have htrace : WordTrace (prefixWord ++ tailWord_1446592) baseStart_1446592 baseEnd_1446592 := by
    simpa [prefixWord, tailWord_1446592, baseEnd_1446592] using wordTrace_append hprefix tailTrace_1446592
  have hstable : (prefixWord ++ tailWord_1446592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446592).length < 2 ^ (prefixWord ++ tailWord_1446592).sum := by decide
  have hdescent : baseEnd_1446592 < baseStart_1446592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446598 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1446598 : Nat := 118140960795 + 1446598 * 2 ^ 59
def prefixEnd_1446598 : Nat := 4983230072969 + 3 ^ 40 * 1446598 * 2
def baseEnd_1446598 : Nat := 330133372370149516609877

theorem tailTrace_1446598 : CollatzResearch.WordTrace tailWord_1446598 prefixEnd_1446598 330133372370149516609877 := by
  unfold tailWord_1446598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648805112913436878566139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35174509075486653409410965 1648805112913436878566139)
  ·
    refine ⟨2473207669370155317849209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1648805112913436878566139 2473207669370155317849209)
    ·
      refine ⟨1854905752027616488386907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2473207669370155317849209 1854905752027616488386907)
      ·
        refine ⟨2782358628041424732580361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1854905752027616488386907 2782358628041424732580361)
        ·
          refine ⟨2086768971031068549435271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2782358628041424732580361 2086768971031068549435271)
          ·
            refine ⟨3130153456546602824152907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086768971031068549435271 3130153456546602824152907)
            ·
              refine ⟨4695230184819904236229361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130153456546602824152907 4695230184819904236229361)
              ·
                refine ⟨3521422638614928177172021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4695230184819904236229361 3521422638614928177172021)
                ·
                  refine ⟨330133372370149516609877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3521422638614928177172021 330133372370149516609877)
                  ·
                    rfl

theorem cell21_1446598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1446598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446598 prefixEnd_1446598 := by exact prefixLift 1446598
  have htrace : WordTrace (prefixWord ++ tailWord_1446598) baseStart_1446598 baseEnd_1446598 := by
    simpa [prefixWord, tailWord_1446598, baseEnd_1446598] using wordTrace_append hprefix tailTrace_1446598
  have hstable : (prefixWord ++ tailWord_1446598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446598).length < 2 ^ (prefixWord ++ tailWord_1446598).sum := by decide
  have hdescent : baseEnd_1446598 < baseStart_1446598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446792 : List Nat := [2, 1, 3, 3, 2, 1, 1, 5, 3]
def baseStart_1446792 : Nat := 118140960795 + 1446792 * 2 ^ 59
def prefixEnd_1446792 : Nat := 4983230072969 + 3 ^ 40 * 1446792 * 2
def baseEnd_1446792 : Nat := 330177645813248290376147

theorem tailTrace_1446792 : CollatzResearch.WordTrace tailWord_1446792 prefixEnd_1446792 330177645813248290376147 := by
  unfold tailWord_1446792
  simp only [CollatzResearch.WordTrace]
  refine ⟨26384419687263575623339315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35179226249684767497785753 26384419687263575623339315)
  ·
    refine ⟨39576629530895363435008973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26384419687263575623339315 39576629530895363435008973)
    ·
      refine ⟨14841236074085761288128365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39576629530895363435008973 14841236074085761288128365)
      ·
        refine ⟨5565463527782160483048137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14841236074085761288128365 5565463527782160483048137)
        ·
          refine ⟨4174097645836620362286103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5565463527782160483048137 4174097645836620362286103)
          ·
            refine ⟨6261146468754930543429155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174097645836620362286103 6261146468754930543429155)
            ·
              refine ⟨9391719703132395815143733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261146468754930543429155 9391719703132395815143733)
              ·
                refine ⟨880473722168662107669725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9391719703132395815143733 880473722168662107669725)
                ·
                  refine ⟨330177645813248290376147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880473722168662107669725 330177645813248290376147)
                  ·
                    rfl

theorem cell21_1446792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 3].length) (baseStart_1446792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446792 prefixEnd_1446792 := by exact prefixLift 1446792
  have htrace : WordTrace (prefixWord ++ tailWord_1446792) baseStart_1446792 baseEnd_1446792 := by
    simpa [prefixWord, tailWord_1446792, baseEnd_1446792] using wordTrace_append hprefix tailTrace_1446792
  have hstable : (prefixWord ++ tailWord_1446792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446792).length < 2 ^ (prefixWord ++ tailWord_1446792).sum := by decide
  have hdescent : baseEnd_1446792 < baseStart_1446792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446865 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 4]
def baseStart_1446865 : Nat := 118140960795 + 1446865 * 2 ^ 59
def prefixEnd_1446865 : Nat := 4983230072969 + 3 ^ 40 * 1446865 * 2
def baseEnd_1446865 : Nat := 330194305407816385659331

theorem tailTrace_1446865 : CollatzResearch.WordTrace tailWord_1446865 prefixEnd_1446865 330194305407816385659331 := by
  unfold tailWord_1446865
  simp only [CollatzResearch.WordTrace]
  refine ⟨52771501903262684714086049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35181001268841789809390699 52771501903262684714086049)
  ·
    refine ⟨39578626427447013535564537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52771501903262684714086049 39578626427447013535564537)
    ·
      refine ⟨29683969820585260151673403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39578626427447013535564537 29683969820585260151673403)
      ·
        refine ⟨44525954730877890227510105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29683969820585260151673403 44525954730877890227510105)
        ·
          refine ⟨33394466048158417670632579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44525954730877890227510105 33394466048158417670632579)
          ·
            refine ⟨50091699072237626505948869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33394466048158417670632579 50091699072237626505948869)
            ·
              refine ⟨9392193576044554969865413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50091699072237626505948869 9392193576044554969865413)
              ·
                refine ⟨1761036295508354056849765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9392193576044554969865413 1761036295508354056849765)
                ·
                  refine ⟨330194305407816385659331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1761036295508354056849765 330194305407816385659331)
                  ·
                    rfl

theorem cell21_1446865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_1446865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446865 prefixEnd_1446865 := by exact prefixLift 1446865
  have htrace : WordTrace (prefixWord ++ tailWord_1446865) baseStart_1446865 baseEnd_1446865 := by
    simpa [prefixWord, tailWord_1446865, baseEnd_1446865] using wordTrace_append hprefix tailTrace_1446865
  have hstable : (prefixWord ++ tailWord_1446865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446865).length < 2 ^ (prefixWord ++ tailWord_1446865).sum := by decide
  have hdescent : baseEnd_1446865 < baseStart_1446865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446868 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1446868 : Nat := 118140960795 + 1446868 * 2 ^ 59
def prefixEnd_1446868 : Nat := 4983230072969 + 3 ^ 40 * 1446868 * 2
def baseEnd_1446868 : Nat := 330194990048689047109325

theorem tailTrace_1446868 : CollatzResearch.WordTrace tailWord_1446868 prefixEnd_1446868 330194990048689047109325 := by
  unfold tailWord_1446868
  simp only [CollatzResearch.WordTrace]
  refine ⟨26385805661125908113222629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35181074214834544150963505 26385805661125908113222629)
  ·
    refine ⟨4947338561461107771229243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26385805661125908113222629 4947338561461107771229243)
    ·
      refine ⟨7421007842191661656843865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4947338561461107771229243 7421007842191661656843865)
      ·
        refine ⟨5565755881643746242632899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7421007842191661656843865 5565755881643746242632899)
        ·
          refine ⟨8348633822465619363949349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5565755881643746242632899 8348633822465619363949349)
          ·
            refine ⟨1565368841712303630740503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8348633822465619363949349 1565368841712303630740503)
            ·
              refine ⟨2348053262568455446110755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565368841712303630740503 2348053262568455446110755)
              ·
                refine ⟨3522079893852683169166133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348053262568455446110755 3522079893852683169166133)
                ·
                  refine ⟨330194990048689047109325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3522079893852683169166133 330194990048689047109325)
                  ·
                    rfl

theorem cell21_1446868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1446868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446868 prefixEnd_1446868 := by exact prefixLift 1446868
  have htrace : WordTrace (prefixWord ++ tailWord_1446868) baseStart_1446868 baseEnd_1446868 := by
    simpa [prefixWord, tailWord_1446868, baseEnd_1446868] using wordTrace_append hprefix tailTrace_1446868
  have hstable : (prefixWord ++ tailWord_1446868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446868).length < 2 ^ (prefixWord ++ tailWord_1446868).sum := by decide
  have hdescent : baseEnd_1446868 < baseStart_1446868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446944 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 5]
def baseStart_1446944 : Nat := 118140960795 + 1446944 * 2 ^ 59
def prefixEnd_1446944 : Nat := 4983230072969 + 3 ^ 40 * 1446944 * 2
def baseEnd_1446944 : Nat := 330212334284129803842503

theorem tailTrace_1446944 : CollatzResearch.WordTrace tailWord_1446944 prefixEnd_1446944 330212334284129803842503 := by
  unfold tailWord_1446944
  simp only [CollatzResearch.WordTrace]
  refine ⟨26387191634988240603105943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35182922179984320804141257 26387191634988240603105943)
  ·
    refine ⟨39580787452482360904658915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26387191634988240603105943 39580787452482360904658915)
    ·
      refine ⟨59371181178723541356988373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39580787452482360904658915 59371181178723541356988373)
      ·
        refine ⟨1391512058876333000554415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 59371181178723541356988373 1391512058876333000554415)
        ·
          refine ⟨2087268088314499500831623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1391512058876333000554415 2087268088314499500831623)
          ·
            refine ⟨3130902132471749251247435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087268088314499500831623 3130902132471749251247435)
            ·
              refine ⟨4696353198707623876871153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130902132471749251247435 4696353198707623876871153)
              ·
                refine ⟨3522264899030717907653365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4696353198707623876871153 3522264899030717907653365)
                ·
                  refine ⟨330212334284129803842503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3522264899030717907653365 330212334284129803842503)
                  ·
                    rfl

theorem cell21_1446944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_1446944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446944 prefixEnd_1446944 := by exact prefixLift 1446944
  have htrace : WordTrace (prefixWord ++ tailWord_1446944) baseStart_1446944 baseEnd_1446944 := by
    simpa [prefixWord, tailWord_1446944, baseEnd_1446944] using wordTrace_append hprefix tailTrace_1446944
  have hstable : (prefixWord ++ tailWord_1446944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446944).length < 2 ^ (prefixWord ++ tailWord_1446944).sum := by decide
  have hdescent : baseEnd_1446944 < baseStart_1446944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446986 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_1446986 : Nat := 118140960795 + 1446986 * 2 ^ 59
def prefixEnd_1446986 : Nat := 4983230072969 + 3 ^ 40 * 1446986 * 2
def baseEnd_1446986 : Nat := 330221919256347064142417

theorem tailTrace_1446986 : CollatzResearch.WordTrace tailWord_1446986 prefixEnd_1446986 330221919256347064142417 := by
  unfold tailWord_1446986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13193978783956080594810203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35183943423882881586160541 13193978783956080594810203)
  ·
    refine ⟨19790968175934120892215305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13193978783956080594810203 19790968175934120892215305)
    ·
      refine ⟨14843226131950590669161479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19790968175934120892215305 14843226131950590669161479)
      ·
        refine ⟨22264839197925886003742219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14843226131950590669161479 22264839197925886003742219)
        ·
          refine ⟨33397258796888829005613329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22264839197925886003742219 33397258796888829005613329)
          ·
            refine ⟨25047944097666621754209997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33397258796888829005613329 25047944097666621754209997)
            ·
              refine ⟨9392979036624983157828749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25047944097666621754209997 9392979036624983157828749)
              ·
                refine ⟨3522367138734368684185781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9392979036624983157828749 3522367138734368684185781)
                ·
                  refine ⟨330221919256347064142417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3522367138734368684185781 330221919256347064142417)
                  ·
                    rfl

theorem cell21_1446986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_1446986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1446986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1446986 prefixEnd_1446986 := by exact prefixLift 1446986
  have htrace : WordTrace (prefixWord ++ tailWord_1446986) baseStart_1446986 baseEnd_1446986 := by
    simpa [prefixWord, tailWord_1446986, baseEnd_1446986] using wordTrace_append hprefix tailTrace_1446986
  have hstable : (prefixWord ++ tailWord_1446986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446986).length < 2 ^ (prefixWord ++ tailWord_1446986).sum := by decide
  have hdescent : baseEnd_1446986 < baseStart_1446986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447006 : List Nat := [4, 4, 1, 1, 1, 2, 1, 7]
def baseStart_1447006 : Nat := 118140960795 + 1447006 * 2 ^ 59
def prefixEnd_1447006 : Nat := 4983230072969 + 3 ^ 40 * 1447006 * 2
def baseEnd_1447006 : Nat := 110075494509610491269681

theorem tailTrace_1447006 : CollatzResearch.WordTrace tailWord_1447006 prefixEnd_1447006 110075494509610491269681 := by
  unfold tailWord_1447006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6597080574468983224371109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35184429730501243863312581 6597080574468983224371109)
  ·
    refine ⟨1236952607712934354569583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6597080574468983224371109 1236952607712934354569583)
    ·
      refine ⟨1855428911569401531854375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236952607712934354569583 1855428911569401531854375)
      ·
        refine ⟨2783143367354102297781563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855428911569401531854375 2783143367354102297781563)
        ·
          refine ⟨4174715051031153446672345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783143367354102297781563 4174715051031153446672345)
          ·
            refine ⟨3131036288273365085004259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4174715051031153446672345 3131036288273365085004259)
            ·
              refine ⟨4696554432410047627506389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131036288273365085004259 4696554432410047627506389)
              ·
                refine ⟨110075494509610491269681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4696554432410047627506389 110075494509610491269681)
                ·
                  rfl

theorem cell21_1447006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_1447006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447006 prefixEnd_1447006 := by exact prefixLift 1447006
  have htrace : WordTrace (prefixWord ++ tailWord_1447006) baseStart_1447006 baseEnd_1447006 := by
    simpa [prefixWord, tailWord_1447006, baseEnd_1447006] using wordTrace_append hprefix tailTrace_1447006
  have hstable : (prefixWord ++ tailWord_1447006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447006).length < 2 ^ (prefixWord ++ tailWord_1447006).sum := by decide
  have hdescent : baseEnd_1447006 < baseStart_1447006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
