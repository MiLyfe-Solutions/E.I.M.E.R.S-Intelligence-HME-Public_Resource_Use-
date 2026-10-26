import V185TrunkScan23Chunk0579

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3430080 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 6]
def baseStart_3430080 : Nat := 118140960795 + 3430080 * 2 ^ 59
def prefixEnd_3430080 : Nat := 4983230072969 + 3 ^ 40 * 3430080 * 2
def baseEnd_3430080 : Nat := 195697747041560558880595

theorem tailTrace_3430080 : CollatzResearch.WordTrace tailWord_3430080 prefixEnd_3430080 195697747041560558880595 := by
  unfold tailWord_3430080
  simp only [CollatzResearch.WordTrace]
  refine ⟨62552647706706722935155847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83403530275608963913541129 62552647706706722935155847)
  ·
    refine ⟨93828971560060084402733771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62552647706706722935155847 93828971560060084402733771)
    ·
      refine ⟨140743457340090126604100657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93828971560060084402733771 140743457340090126604100657)
      ·
        refine ⟨105557593005067594953075493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140743457340090126604100657 105557593005067594953075493)
        ·
          refine ⟨19792048688450174053701655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105557593005067594953075493 19792048688450174053701655)
          ·
            refine ⟨29688073032675261080552483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19792048688450174053701655 29688073032675261080552483)
            ·
              refine ⟨44532109549012891620828725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29688073032675261080552483 44532109549012891620828725)
              ·
                refine ⟨4174885270219958589452693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44532109549012891620828725 4174885270219958589452693)
                ·
                  refine ⟨195697747041560558880595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4174885270219958589452693 195697747041560558880595)
                  ·
                    rfl

theorem cell23_3430080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 6].length) (baseStart_3430080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430080 prefixEnd_3430080 := by exact prefixLift 3430080
  have htrace : WordTrace (prefixWord ++ tailWord_3430080) baseStart_3430080 baseEnd_3430080 := by
    simpa [prefixWord, tailWord_3430080, baseEnd_3430080] using wordTrace_append hprefix tailTrace_3430080
  have hstable : (prefixWord ++ tailWord_3430080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430080).length < 2 ^ (prefixWord ++ tailWord_3430080).sum := by decide
  have hdescent : baseEnd_3430080 < baseStart_3430080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430134 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_3430134 : Nat := 118140960795 + 3430134 * 2 ^ 59
def prefixEnd_3430134 : Nat := 4983230072969 + 3 ^ 40 * 3430134 * 2
def baseEnd_3430134 : Nat := 1761307451329387818650107

theorem tailTrace_3430134 : CollatzResearch.WordTrace tailWord_3430134 prefixEnd_3430134 1761307451329387818650107 := by
  unfold tailWord_3430134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7819204059701113318298591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83404843303478542061851637 7819204059701113318298591)
  ·
    refine ⟨11728806089551669977447887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7819204059701113318298591 11728806089551669977447887)
    ·
      refine ⟨17593209134327504966171831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11728806089551669977447887 17593209134327504966171831)
      ·
        refine ⟨26389813701491257449257747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17593209134327504966171831 26389813701491257449257747)
        ·
          refine ⟨39584720552236886173886621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26389813701491257449257747 39584720552236886173886621)
          ·
            refine ⟨14844270207088832315207483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39584720552236886173886621 14844270207088832315207483)
            ·
              refine ⟨22266405310633248472811225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14844270207088832315207483 22266405310633248472811225)
              ·
                refine ⟨16699803982974936354608419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22266405310633248472811225 16699803982974936354608419)
                ·
                  refine ⟨25049705974462404531912629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16699803982974936354608419 25049705974462404531912629)
                  ·
                    refine ⟨2348409935105850424866809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25049705974462404531912629 2348409935105850424866809)
                    ·
                      refine ⟨1761307451329387818650107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2348409935105850424866809 1761307451329387818650107)
                      ·
                        rfl

theorem cell23_3430134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_3430134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430134 prefixEnd_3430134 := by exact prefixLift 3430134
  have htrace : WordTrace (prefixWord ++ tailWord_3430134) baseStart_3430134 baseEnd_3430134 := by
    simpa [prefixWord, tailWord_3430134, baseEnd_3430134] using wordTrace_append hprefix tailTrace_3430134
  have hstable : (prefixWord ++ tailWord_3430134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430134).length < 2 ^ (prefixWord ++ tailWord_3430134).sum := by decide
  have hdescent : baseEnd_3430134 < baseStart_3430134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430147 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 4]
def baseStart_3430147 : Nat := 118140960795 + 3430147 * 2 ^ 59
def prefixEnd_3430147 : Nat := 4983230072969 + 3 ^ 40 * 3430147 * 2
def baseEnd_3430147 : Nat := 1761314126577896267787547

theorem tailTrace_3430147 : CollatzResearch.WordTrace tailWord_3430147 prefixEnd_3430147 1761314126577896267787547 := by
  unfold tailWord_3430147
  simp only [CollatzResearch.WordTrace]
  refine ⟨125107739104170716313000695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83405159402780477542000463 125107739104170716313000695)
  ·
    refine ⟨187661608656256074469501043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125107739104170716313000695 187661608656256074469501043)
    ·
      refine ⟨281492412984384111704251565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187661608656256074469501043 281492412984384111704251565)
      ·
        refine ⟨105559654869144041889094337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281492412984384111704251565 105559654869144041889094337)
        ·
          refine ⟨79169741151858031416820753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105559654869144041889094337 79169741151858031416820753)
          ·
            refine ⟨59377305863893523562615565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79169741151858031416820753 59377305863893523562615565)
            ·
              refine ⟨22266489698960071335980837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59377305863893523562615565 22266489698960071335980837)
              ·
                refine ⟨4174966818555013375496407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22266489698960071335980837 4174966818555013375496407)
                ·
                  refine ⟨6262450227832520063244611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4174966818555013375496407 6262450227832520063244611)
                  ·
                    refine ⟨9393675341748780094866917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6262450227832520063244611 9393675341748780094866917)
                    ·
                      refine ⟨1761314126577896267787547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9393675341748780094866917 1761314126577896267787547)
                      ·
                        rfl

theorem cell23_3430147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_3430147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430147 prefixEnd_3430147 := by exact prefixLift 3430147
  have htrace : WordTrace (prefixWord ++ tailWord_3430147) baseStart_3430147 baseEnd_3430147 := by
    simpa [prefixWord, tailWord_3430147, baseEnd_3430147] using wordTrace_append hprefix tailTrace_3430147
  have hstable : (prefixWord ++ tailWord_3430147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430147).length < 2 ^ (prefixWord ++ tailWord_3430147).sum := by decide
  have hdescent : baseEnd_3430147 < baseStart_3430147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430167 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3430167 : Nat := 118140960795 + 3430167 * 2 ^ 59
def prefixEnd_3430167 : Nat := 4983230072969 + 3 ^ 40 * 3430167 * 2
def baseEnd_3430167 : Nat := 1761324396190986189537455

theorem tailTrace_3430167 : CollatzResearch.WordTrace tailWord_3430167 prefixEnd_3430167 1761324396190986189537455 := by
  unfold tailWord_3430167
  simp only [CollatzResearch.WordTrace]
  refine ⟨125108468564098259728728755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83405645709398839819152503 125108468564098259728728755)
  ·
    refine ⟨187662702846147389593093133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125108468564098259728728755 187662702846147389593093133)
    ·
      refine ⟨70373513567305271097409925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187662702846147389593093133 70373513567305271097409925)
      ·
        refine ⟨13195033793869738330764361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70373513567305271097409925 13195033793869738330764361)
        ·
          refine ⟨9896275345402303748073271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13195033793869738330764361 9896275345402303748073271)
          ·
            refine ⟨14844413018103455622109907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9896275345402303748073271 14844413018103455622109907)
            ·
              refine ⟨22266619527155183433164861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14844413018103455622109907 22266619527155183433164861)
              ·
                refine ⟨8349982322683193787436823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22266619527155183433164861 8349982322683193787436823)
                ·
                  refine ⟨12524973484024790681155235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8349982322683193787436823 12524973484024790681155235)
                  ·
                    refine ⟨18787460226037186021732853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12524973484024790681155235 18787460226037186021732853)
                    ·
                      refine ⟨1761324396190986189537455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18787460226037186021732853 1761324396190986189537455)
                      ·
                        rfl

theorem cell23_3430167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3430167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430167 prefixEnd_3430167 := by exact prefixLift 3430167
  have htrace : WordTrace (prefixWord ++ tailWord_3430167) baseStart_3430167 baseEnd_3430167 := by
    simpa [prefixWord, tailWord_3430167, baseEnd_3430167] using wordTrace_append hprefix tailTrace_3430167
  have hstable : (prefixWord ++ tailWord_3430167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430167).length < 2 ^ (prefixWord ++ tailWord_3430167).sum := by decide
  have hdescent : baseEnd_3430167 < baseStart_3430167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430170 : List Nat := [3, 1, 1, 3, 2, 2, 11]
def baseStart_3430170 : Nat := 118140960795 + 3430170 * 2 ^ 59
def prefixEnd_3430170 : Nat := 4983230072969 + 3 ^ 40 * 3430170 * 2
def baseEnd_3430170 : Nat := 21744764649789502195061

theorem tailTrace_3430170 : CollatzResearch.WordTrace tailWord_3430170 prefixEnd_3430170 21744764649789502195061 := by
  unfold tailWord_3430170
  simp only [CollatzResearch.WordTrace]
  refine ⟨31277144495771847810271991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83405718655391594160725309 31277144495771847810271991)
  ·
    refine ⟨46915716743657771715407987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31277144495771847810271991 46915716743657771715407987)
    ·
      refine ⟨70373575115486657573111981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46915716743657771715407987 70373575115486657573111981)
      ·
        refine ⟨26390090668307496589916993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70373575115486657573111981 26390090668307496589916993)
        ·
          refine ⟨19792568001230622442437745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26390090668307496589916993 19792568001230622442437745)
          ·
            refine ⟨14844426000922966831828309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19792568001230622442437745 14844426000922966831828309)
            ·
              refine ⟨21744764649789502195061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14844426000922966831828309 21744764649789502195061)
              ·
                rfl

theorem cell23_3430170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 11].length) (baseStart_3430170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430170 prefixEnd_3430170 := by exact prefixLift 3430170
  have htrace : WordTrace (prefixWord ++ tailWord_3430170) baseStart_3430170 baseEnd_3430170 := by
    simpa [prefixWord, tailWord_3430170, baseEnd_3430170] using wordTrace_append hprefix tailTrace_3430170
  have hstable : (prefixWord ++ tailWord_3430170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430170).length < 2 ^ (prefixWord ++ tailWord_3430170).sum := by decide
  have hdescent : baseEnd_3430170 < baseStart_3430170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430181 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 3, 2, 2]
def baseStart_3430181 : Nat := 118140960795 + 3430181 * 2 ^ 59
def prefixEnd_3430181 : Nat := 4983230072969 + 3 ^ 40 * 3430181 * 2
def baseEnd_3430181 : Nat := 1761331584920149134762391

theorem tailTrace_3430181 : CollatzResearch.WordTrace tailWord_3430181 prefixEnd_3430181 1761331584920149134762391 := by
  unfold tailWord_3430181
  simp only [CollatzResearch.WordTrace]
  refine ⟨125108979186047540119738397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83405986124031693413158931 125108979186047540119738397)
  ·
    refine ⟨46915867194767827544901899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125108979186047540119738397 46915867194767827544901899)
    ·
      refine ⟨70373800792151741317352849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46915867194767827544901899 70373800792151741317352849)
      ·
        refine ⟨52780350594113805988014637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70373800792151741317352849 52780350594113805988014637)
        ·
          refine ⟨19792631472792677245505489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52780350594113805988014637 19792631472792677245505489)
          ·
            refine ⟨14844473604594507934129117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19792631472792677245505489 14844473604594507934129117)
            ·
              refine ⟨5566677601722940475298419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14844473604594507934129117 5566677601722940475298419)
              ·
                refine ⟨8350016402584410712947629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566677601722940475298419 8350016402584410712947629)
                ·
                  refine ⟨3131256150969154017355361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8350016402584410712947629 3131256150969154017355361)
                  ·
                    refine ⟨2348442113226865513016521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3131256150969154017355361 2348442113226865513016521)
                    ·
                      refine ⟨1761331584920149134762391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2348442113226865513016521 1761331584920149134762391)
                      ·
                        rfl

theorem cell23_3430181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_3430181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430181 prefixEnd_3430181 := by exact prefixLift 3430181
  have htrace : WordTrace (prefixWord ++ tailWord_3430181) baseStart_3430181 baseEnd_3430181 := by
    simpa [prefixWord, tailWord_3430181, baseEnd_3430181] using wordTrace_append hprefix tailTrace_3430181
  have hstable : (prefixWord ++ tailWord_3430181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430181).length < 2 ^ (prefixWord ++ tailWord_3430181).sum := by decide
  have hdescent : baseEnd_3430181 < baseStart_3430181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430198 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3430198 : Nat := 118140960795 + 3430198 * 2 ^ 59
def prefixEnd_3430198 : Nat := 4983230072969 + 3 ^ 40 * 3430198 * 2
def baseEnd_3430198 : Nat := 1761340314091275568249813

theorem tailTrace_3430198 : CollatzResearch.WordTrace tailWord_3430198 prefixEnd_3430198 1761340314091275568249813 := by
  unfold tailWord_3430198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7819349951686622001444203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83406399484657301348738165 7819349951686622001444203)
  ·
    refine ⟨11729024927529933002166305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7819349951686622001444203 11729024927529933002166305)
    ·
      refine ⟨8796768695647449751624729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11729024927529933002166305 8796768695647449751624729)
      ·
        refine ⟨6597576521735587313718547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8796768695647449751624729 6597576521735587313718547)
        ·
          refine ⟨9896364782603380970577821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6597576521735587313718547 9896364782603380970577821)
          ·
            refine ⟨3711136793476267863966683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9896364782603380970577821 3711136793476267863966683)
            ·
              refine ⟨5566705190214401795950025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711136793476267863966683 5566705190214401795950025)
              ·
                refine ⟨4175028892660801346962519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5566705190214401795950025 4175028892660801346962519)
                ·
                  refine ⟨6262543338991202020443779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4175028892660801346962519 6262543338991202020443779)
                  ·
                    refine ⟨9393815008486803030665669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6262543338991202020443779 9393815008486803030665669)
                    ·
                      refine ⟨1761340314091275568249813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9393815008486803030665669 1761340314091275568249813)
                      ·
                        rfl

theorem cell23_3430198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3430198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430198 prefixEnd_3430198 := by exact prefixLift 3430198
  have htrace : WordTrace (prefixWord ++ tailWord_3430198) baseStart_3430198 baseEnd_3430198 := by
    simpa [prefixWord, tailWord_3430198, baseEnd_3430198] using wordTrace_append hprefix tailTrace_3430198
  have hstable : (prefixWord ++ tailWord_3430198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430198).length < 2 ^ (prefixWord ++ tailWord_3430198).sum := by decide
  have hdescent : baseEnd_3430198 < baseStart_3430198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430201 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3430201 : Nat := 118140960795 + 3430201 * 2 ^ 59
def prefixEnd_3430201 : Nat := 4983230072969 + 3 ^ 40 * 3430201 * 2
def baseEnd_3430201 : Nat := 1761341854533239056512299

theorem tailTrace_3430201 : CollatzResearch.WordTrace tailWord_3430201 prefixEnd_3430201 1761341854533239056512299 := by
  unfold tailWord_3430201
  simp only [CollatzResearch.WordTrace]
  refine ⟨125109708645975083535466457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83406472430650055690310971 125109708645975083535466457)
  ·
    refine ⟨93832281484481312651599843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125109708645975083535466457 93832281484481312651599843)
    ·
      refine ⟨140748422226721968977399765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93832281484481312651599843 140748422226721968977399765)
      ·
        refine ⟨3298791145938796147907807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 140748422226721968977399765 3298791145938796147907807)
        ·
          refine ⟨4948186718908194221861711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3298791145938796147907807 4948186718908194221861711)
          ·
            refine ⟨7422280078362291332792567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948186718908194221861711 7422280078362291332792567)
            ·
              refine ⟨11133420117543436999188851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422280078362291332792567 11133420117543436999188851)
              ·
                refine ⟨16700130176315155498783277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11133420117543436999188851 16700130176315155498783277)
                ·
                  refine ⟨6262548816118183312043729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16700130176315155498783277 6262548816118183312043729)
                  ·
                    refine ⟨4696911612088637484032797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6262548816118183312043729 4696911612088637484032797)
                    ·
                      refine ⟨1761341854533239056512299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4696911612088637484032797 1761341854533239056512299)
                      ·
                        rfl

theorem cell23_3430201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3430201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430201 prefixEnd_3430201 := by exact prefixLift 3430201
  have htrace : WordTrace (prefixWord ++ tailWord_3430201) baseStart_3430201 baseEnd_3430201 := by
    simpa [prefixWord, tailWord_3430201, baseEnd_3430201] using wordTrace_append hprefix tailTrace_3430201
  have hstable : (prefixWord ++ tailWord_3430201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430201).length < 2 ^ (prefixWord ++ tailWord_3430201).sum := by decide
  have hdescent : baseEnd_3430201 < baseStart_3430201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430247 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 2, 6]
def baseStart_3430247 : Nat := 118140960795 + 3430247 * 2 ^ 59
def prefixEnd_3430247 : Nat := 4983230072969 + 3 ^ 40 * 3430247 * 2
def baseEnd_3430247 : Nat := 587121824881115292179029

theorem tailTrace_3430247 : CollatzResearch.WordTrace tailWord_3430247 prefixEnd_3430247 587121824881115292179029 := by
  unfold tailWord_3430247
  simp only [CollatzResearch.WordTrace]
  refine ⟨125111386403808433391640995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83407590935872288927760663 125111386403808433391640995)
  ·
    refine ⟨187667079605712650087461493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125111386403808433391640995 187667079605712650087461493)
    ·
      refine ⟨17593788713035560945699515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187667079605712650087461493 17593788713035560945699515)
      ·
        refine ⟨26390683069553341418549273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17593788713035560945699515 26390683069553341418549273)
        ·
          refine ⟨19793012302165006063911955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26390683069553341418549273 19793012302165006063911955)
          ·
            refine ⟨29689518453247509095867933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19793012302165006063911955 29689518453247509095867933)
            ·
              refine ⟨11133569419967815910950475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29689518453247509095867933 11133569419967815910950475)
              ·
                refine ⟨16700354129951723866425713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11133569419967815910950475 16700354129951723866425713)
                ·
                  refine ⟨12525265597463792899819285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16700354129951723866425713 12525265597463792899819285)
                  ·
                    refine ⟨587121824881115292179029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12525265597463792899819285 587121824881115292179029)
                    ·
                      rfl

theorem cell23_3430247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_3430247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430247 prefixEnd_3430247 := by exact prefixLift 3430247
  have htrace : WordTrace (prefixWord ++ tailWord_3430247) baseStart_3430247 baseEnd_3430247 := by
    simpa [prefixWord, tailWord_3430247, baseEnd_3430247] using wordTrace_append hprefix tailTrace_3430247
  have hstable : (prefixWord ++ tailWord_3430247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430247).length < 2 ^ (prefixWord ++ tailWord_3430247).sum := by decide
  have hdescent : baseEnd_3430247 < baseStart_3430247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430257 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 2, 4, 3]
def baseStart_3430257 : Nat := 118140960795 + 3430257 * 2 ^ 59
def prefixEnd_3430257 : Nat := 4983230072969 + 3 ^ 40 * 3430257 * 2
def baseEnd_3430257 : Nat := 1761370609449890837412041

theorem tailTrace_3430257 : CollatzResearch.WordTrace tailWord_3430257 prefixEnd_3430257 1761370609449890837412041 := by
  unfold tailWord_3430257
  simp only [CollatzResearch.WordTrace]
  refine ⟨125111751133772205099505025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83407834089181470066336683 125111751133772205099505025)
  ·
    refine ⟨93833813350329153824628769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125111751133772205099505025 93833813350329153824628769)
    ·
      refine ⟨70375360012746865368471577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93833813350329153824628769 70375360012746865368471577)
      ·
        refine ⟨52781520009560149026353683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70375360012746865368471577 52781520009560149026353683)
        ·
          refine ⟨79172280014340223539530525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52781520009560149026353683 79172280014340223539530525)
          ·
            refine ⟨29689605005377583827323947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79172280014340223539530525 29689605005377583827323947)
            ·
              refine ⟨44534407508066375740985921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29689605005377583827323947 44534407508066375740985921)
              ·
                refine ⟨33400805631049781805739441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44534407508066375740985921 33400805631049781805739441)
                ·
                  refine ⟨25050604223287336354304581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33400805631049781805739441 25050604223287336354304581)
                  ·
                    refine ⟨4696988291866375566432109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25050604223287336354304581 4696988291866375566432109)
                    ·
                      refine ⟨1761370609449890837412041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4696988291866375566432109 1761370609449890837412041)
                      ·
                        rfl

theorem cell23_3430257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_3430257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430257 prefixEnd_3430257 := by exact prefixLift 3430257
  have htrace : WordTrace (prefixWord ++ tailWord_3430257) baseStart_3430257 baseEnd_3430257 := by
    simpa [prefixWord, tailWord_3430257, baseEnd_3430257] using wordTrace_append hprefix tailTrace_3430257
  have hstable : (prefixWord ++ tailWord_3430257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430257).length < 2 ^ (prefixWord ++ tailWord_3430257).sum := by decide
  have hdescent : baseEnd_3430257 < baseStart_3430257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430305 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 1, 4, 2]
def baseStart_3430305 : Nat := 118140960795 + 3430305 * 2 ^ 59
def prefixEnd_3430305 : Nat := 4983230072969 + 3 ^ 40 * 3430305 * 2
def baseEnd_3430305 : Nat := 1761395256521306649611821

theorem tailTrace_3430305 : CollatzResearch.WordTrace tailWord_3430305 prefixEnd_3430305 1761395256521306649611821 := by
  unfold tailWord_3430305
  simp only [CollatzResearch.WordTrace]
  refine ⟨125113501837598309297252369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83409001225065539531501579 125113501837598309297252369)
  ·
    refine ⟨93835126378198731972939277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125113501837598309297252369 93835126378198731972939277)
    ·
      refine ⟨35188172391824524489852229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93835126378198731972939277 35188172391824524489852229)
      ·
        refine ⟨6597782323467098341847293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35188172391824524489852229 6597782323467098341847293)
        ·
          refine ⟨2474168371300161878192735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6597782323467098341847293 2474168371300161878192735)
          ·
            refine ⟨3711252556950242817289103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474168371300161878192735 3711252556950242817289103)
            ·
              refine ⟨5566878835425364225933655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711252556950242817289103 5566878835425364225933655)
              ·
                refine ⟨8350318253138046338900483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566878835425364225933655 8350318253138046338900483)
                ·
                  refine ⟨12525477379707069508350725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8350318253138046338900483 12525477379707069508350725)
                  ·
                    refine ⟨2348527008695075532815761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12525477379707069508350725 2348527008695075532815761)
                    ·
                      refine ⟨1761395256521306649611821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2348527008695075532815761 1761395256521306649611821)
                      ·
                        rfl

theorem cell23_3430305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_3430305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430305 prefixEnd_3430305 := by exact prefixLift 3430305
  have htrace : WordTrace (prefixWord ++ tailWord_3430305) baseStart_3430305 baseEnd_3430305 := by
    simpa [prefixWord, tailWord_3430305, baseEnd_3430305] using wordTrace_append hprefix tailTrace_3430305
  have hstable : (prefixWord ++ tailWord_3430305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430305).length < 2 ^ (prefixWord ++ tailWord_3430305).sum := by decide
  have hdescent : baseEnd_3430305 < baseStart_3430305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430344 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_3430344 : Nat := 118140960795 + 3430344 * 2 ^ 59
def prefixEnd_3430344 : Nat := 4983230072969 + 3 ^ 40 * 3430344 * 2
def baseEnd_3430344 : Nat := 1761415282266831997024141

theorem tailTrace_3430344 : CollatzResearch.WordTrace tailWord_3430344 prefixEnd_3430344 1761415282266831997024141 := by
  unfold tailWord_3430344
  simp only [CollatzResearch.WordTrace]
  refine ⟨62557462142228509478961043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83409949522971345971948057 62557462142228509478961043)
  ·
    refine ⟨93836193213342764218441565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62557462142228509478961043 93836193213342764218441565)
    ·
      refine ⟨35188572455003536581915587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93836193213342764218441565 35188572455003536581915587)
      ·
        refine ⟨52782858682505304872873381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35188572455003536581915587 52782858682505304872873381)
        ·
          refine ⟨9896786002969744663663759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52782858682505304872873381 9896786002969744663663759)
          ·
            refine ⟨14845179004454616995495639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9896786002969744663663759 14845179004454616995495639)
            ·
              refine ⟨22267768506681925493243459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14845179004454616995495639 22267768506681925493243459)
              ·
                refine ⟨33401652760022888239865189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22267768506681925493243459 33401652760022888239865189)
                ·
                  refine ⟨6262809892504291544974723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33401652760022888239865189 6262809892504291544974723)
                  ·
                    refine ⟨9394214838756437317462085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6262809892504291544974723 9394214838756437317462085)
                    ·
                      refine ⟨1761415282266831997024141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9394214838756437317462085 1761415282266831997024141)
                      ·
                        rfl

theorem cell23_3430344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_3430344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430344 prefixEnd_3430344 := by exact prefixLift 3430344
  have htrace : WordTrace (prefixWord ++ tailWord_3430344) baseStart_3430344 baseEnd_3430344 := by
    simpa [prefixWord, tailWord_3430344, baseEnd_3430344] using wordTrace_append hprefix tailTrace_3430344
  have hstable : (prefixWord ++ tailWord_3430344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430344).length < 2 ^ (prefixWord ++ tailWord_3430344).sum := by decide
  have hdescent : baseEnd_3430344 < baseStart_3430344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430398 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3430398 : Nat := 118140960795 + 3430398 * 2 ^ 59
def prefixEnd_3430398 : Nat := 4983230072969 + 3 ^ 40 * 3430398 * 2
def baseEnd_3430398 : Nat := 1761443010222174785748893

theorem tailTrace_3430398 : CollatzResearch.WordTrace tailWord_3430398 prefixEnd_3430398 1761443010222174785748893 := by
  unfold tailWord_3430398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15639611728282673272548481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83411262550840924120258565 15639611728282673272548481)
  ·
    refine ⟨11729708796212004954411361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15639611728282673272548481 11729708796212004954411361)
    ·
      refine ⟨8797281597159003715808521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11729708796212004954411361 8797281597159003715808521)
      ·
        refine ⟨6597961197869252786856391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8797281597159003715808521 6597961197869252786856391)
        ·
          refine ⟨9896941796803879180284587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6597961197869252786856391 9896941796803879180284587)
          ·
            refine ⟨14845412695205818770426881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9896941796803879180284587 14845412695205818770426881)
            ·
              refine ⟨11134059521404364077820161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14845412695205818770426881 11134059521404364077820161)
              ·
                refine ⟨8350544641053273058365121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11134059521404364077820161 8350544641053273058365121)
                ·
                  refine ⟨6262908480789954793773841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8350544641053273058365121 6262908480789954793773841)
                  ·
                    refine ⟨4697181360592466095330381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6262908480789954793773841 4697181360592466095330381)
                    ·
                      refine ⟨1761443010222174785748893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4697181360592466095330381 1761443010222174785748893)
                      ·
                        rfl

theorem cell23_3430398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3430398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430398 prefixEnd_3430398 := by exact prefixLift 3430398
  have htrace : WordTrace (prefixWord ++ tailWord_3430398) baseStart_3430398 baseEnd_3430398 := by
    simpa [prefixWord, tailWord_3430398, baseEnd_3430398] using wordTrace_append hprefix tailTrace_3430398
  have hstable : (prefixWord ++ tailWord_3430398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430398).length < 2 ^ (prefixWord ++ tailWord_3430398).sum := by decide
  have hdescent : baseEnd_3430398 < baseStart_3430398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430405 : List Nat := [1, 3, 1, 1, 2, 6, 2, 2, 1, 4]
def baseStart_3430405 : Nat := 118140960795 + 3430405 * 2 ^ 59
def prefixEnd_3430405 : Nat := 4983230072969 + 3 ^ 40 * 3430405 * 2
def baseEnd_3430405 : Nat := 587148868195585419453787

theorem tailTrace_3430405 : CollatzResearch.WordTrace tailWord_3430405 prefixEnd_3430405 587148868195585419453787 := by
  unfold tailWord_3430405
  simp only [CollatzResearch.WordTrace]
  refine ⟨125117149137236026375892669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83411432758157350917261779 125117149137236026375892669)
  ·
    refine ⟨46918930926463509890959751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125117149137236026375892669 46918930926463509890959751)
    ·
      refine ⟨70378396389695264836439627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46918930926463509890959751 70378396389695264836439627)
      ·
        refine ⟨105567594584542897254659441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70378396389695264836439627 105567594584542897254659441)
        ·
          refine ⟨79175695938407172940994581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105567594584542897254659441 79175695938407172940994581)
          ·
            refine ⟨3711360747112836231609121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79175695938407172940994581 3711360747112836231609121)
            ·
              refine ⟨2783520560334627173706841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3711360747112836231609121 2783520560334627173706841)
              ·
                refine ⟨2087640420250970380280131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2783520560334627173706841 2087640420250970380280131)
                ·
                  refine ⟨3131460630376455570420197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087640420250970380280131 3131460630376455570420197)
                  ·
                    refine ⟨587148868195585419453787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3131460630376455570420197 587148868195585419453787)
                    ·
                      rfl

theorem cell23_3430405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_3430405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430405 prefixEnd_3430405 := by exact prefixLift 3430405
  have htrace : WordTrace (prefixWord ++ tailWord_3430405) baseStart_3430405 baseEnd_3430405 := by
    simpa [prefixWord, tailWord_3430405, baseEnd_3430405] using wordTrace_append hprefix tailTrace_3430405
  have hstable : (prefixWord ++ tailWord_3430405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430405).length < 2 ^ (prefixWord ++ tailWord_3430405).sum := by decide
  have hdescent : baseEnd_3430405 < baseStart_3430405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430411 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 3, 1, 3]
def baseStart_3430411 : Nat := 118140960795 + 3430411 * 2 ^ 59
def prefixEnd_3430411 : Nat := 4983230072969 + 3 ^ 40 * 3430411 * 2
def baseEnd_3430411 : Nat := 1761449685470683234886333

theorem tailTrace_3430411 : CollatzResearch.WordTrace tailWord_3430411 prefixEnd_3430411 1761449685470683234886333 := by
  unfold tailWord_3430411
  simp only [CollatzResearch.WordTrace]
  refine ⟨125117367975214289400611087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83411578650142859600407391 125117367975214289400611087)
  ·
    refine ⟨187676051962821434100916631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125117367975214289400611087 187676051962821434100916631)
    ·
      refine ⟨281514077944232151151374947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187676051962821434100916631 281514077944232151151374947)
      ·
        refine ⟨422271116916348226727062421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281514077944232151151374947 422271116916348226727062421)
        ·
          refine ⟨19793958605453823127831051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 422271116916348226727062421 19793958605453823127831051)
          ·
            refine ⟨29690937908180734691746577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19793958605453823127831051 29690937908180734691746577)
            ·
              refine ⟨22268203431135551018809933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29690937908180734691746577 22268203431135551018809933)
              ·
                refine ⟨8350576286675831632053725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22268203431135551018809933 8350576286675831632053725)
                ·
                  refine ⟨3131466107503436862020147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8350576286675831632053725 3131466107503436862020147)
                  ·
                    refine ⟨4697199161255155293030221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3131466107503436862020147 4697199161255155293030221)
                    ·
                      refine ⟨1761449685470683234886333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4697199161255155293030221 1761449685470683234886333)
                      ·
                        rfl

theorem cell23_3430411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 1, 3].length) (baseStart_3430411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430411 prefixEnd_3430411 := by exact prefixLift 3430411
  have htrace : WordTrace (prefixWord ++ tailWord_3430411) baseStart_3430411 baseEnd_3430411 := by
    simpa [prefixWord, tailWord_3430411, baseEnd_3430411] using wordTrace_append hprefix tailTrace_3430411
  have hstable : (prefixWord ++ tailWord_3430411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430411).length < 2 ^ (prefixWord ++ tailWord_3430411).sum := by decide
  have hdescent : baseEnd_3430411 < baseStart_3430411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430414 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_3430414 : Nat := 118140960795 + 3430414 * 2 ^ 59
def prefixEnd_3430414 : Nat := 4983230072969 + 3 ^ 40 * 3430414 * 2
def baseEnd_3430414 : Nat := 587150408637548907716273

theorem tailTrace_3430414 : CollatzResearch.WordTrace tailWord_3430414 prefixEnd_3430414 587150408637548907716273 := by
  unfold tailWord_3430414
  simp only [CollatzResearch.WordTrace]
  refine ⟨15639684674275427614121287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83411651596135613941980197 15639684674275427614121287)
  ·
    refine ⟨23459527011413141421181931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15639684674275427614121287 23459527011413141421181931)
    ·
      refine ⟨35189290517119712131772897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23459527011413141421181931 35189290517119712131772897)
      ·
        refine ⟨26391967887839784098829673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35189290517119712131772897 26391967887839784098829673)
        ·
          refine ⟨19793975915879838074122255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26391967887839784098829673 19793975915879838074122255)
          ·
            refine ⟨29690963873819757111183383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19793975915879838074122255 29690963873819757111183383)
            ·
              refine ⟨44536445810729635666775075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29690963873819757111183383 44536445810729635666775075)
              ·
                refine ⟨66804668716094453500162613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44536445810729635666775075 66804668716094453500162613)
                ·
                  refine ⟨6262937692133855015640245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66804668716094453500162613 6262937692133855015640245)
                  ·
                    refine ⟨587150408637548907716273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6262937692133855015640245 587150408637548907716273)
                    ·
                      rfl

theorem cell23_3430414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_3430414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430414 prefixEnd_3430414 := by exact prefixLift 3430414
  have htrace : WordTrace (prefixWord ++ tailWord_3430414) baseStart_3430414 baseEnd_3430414 := by
    simpa [prefixWord, tailWord_3430414, baseEnd_3430414] using wordTrace_append hprefix tailTrace_3430414
  have hstable : (prefixWord ++ tailWord_3430414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430414).length < 2 ^ (prefixWord ++ tailWord_3430414).sum := by decide
  have hdescent : baseEnd_3430414 < baseStart_3430414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430428 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_3430428 : Nat := 118140960795 + 3430428 * 2 ^ 59
def prefixEnd_3430428 : Nat := 4983230072969 + 3 ^ 40 * 3430428 * 2
def baseEnd_3430428 : Nat := 1761458414641809668373755

theorem tailTrace_3430428 : CollatzResearch.WordTrace tailWord_3430428 prefixEnd_3430428 1761458414641809668373755 := by
  unfold tailWord_3430428
  simp only [CollatzResearch.WordTrace]
  refine ⟨62558994008076350651989969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83411992010768467535986625 62558994008076350651989969)
  ·
    refine ⟨46919245506057262988992477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62558994008076350651989969 46919245506057262988992477)
    ·
      refine ⟨17594717064771473620872179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46919245506057262988992477 17594717064771473620872179)
      ·
        refine ⟨26392075597157210431308269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17594717064771473620872179 26392075597157210431308269)
        ·
          refine ⟨9897028348933953911740601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26392075597157210431308269 9897028348933953911740601)
          ·
            refine ⟨7422771261700465433805451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9897028348933953911740601 7422771261700465433805451)
            ·
              refine ⟨11134156892550698150708177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422771261700465433805451 11134156892550698150708177)
              ·
                refine ⟨8350617669413023613031133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11134156892550698150708177 8350617669413023613031133)
                ·
                  refine ⟨3131481626029883854886675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8350617669413023613031133 3131481626029883854886675)
                  ·
                    refine ⟨4697222439044825782330013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3131481626029883854886675 4697222439044825782330013)
                    ·
                      refine ⟨1761458414641809668373755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4697222439044825782330013 1761458414641809668373755)
                      ·
                        rfl

theorem cell23_3430428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_3430428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430428 prefixEnd_3430428 := by exact prefixLift 3430428
  have htrace : WordTrace (prefixWord ++ tailWord_3430428) baseStart_3430428 baseEnd_3430428 := by
    simpa [prefixWord, tailWord_3430428, baseEnd_3430428] using wordTrace_append hprefix tailTrace_3430428
  have hstable : (prefixWord ++ tailWord_3430428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430428).length < 2 ^ (prefixWord ++ tailWord_3430428).sum := by decide
  have hdescent : baseEnd_3430428 < baseStart_3430428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430448 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 1, 5]
def baseStart_3430448 : Nat := 118140960795 + 3430448 * 2 ^ 59
def prefixEnd_3430448 : Nat := 4983230072969 + 3 ^ 40 * 3430448 * 2
def baseEnd_3430448 : Nat := 587156228084966530041221

theorem tailTrace_3430448 : CollatzResearch.WordTrace tailWord_3430448 prefixEnd_3430448 587156228084966530041221 := by
  unfold tailWord_3430448
  simp only [CollatzResearch.WordTrace]
  refine ⟨62559358738040122359853999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83412478317386829813138665 62559358738040122359853999)
  ·
    refine ⟨93839038107060183539780999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62559358738040122359853999 93839038107060183539780999)
    ·
      refine ⟨140758557160590275309671499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93839038107060183539780999 140758557160590275309671499)
      ·
        refine ⟨211137835740885412964507249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140758557160590275309671499 211137835740885412964507249)
        ·
          refine ⟨158353376805664059723380437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211137835740885412964507249 158353376805664059723380437)
          ·
            refine ⟨3711407268882751399766729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 158353376805664059723380437 3711407268882751399766729)
            ·
              refine ⟨2783555451662063549825047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3711407268882751399766729 2783555451662063549825047)
              ·
                refine ⟨4175333177493095324737571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2783555451662063549825047 4175333177493095324737571)
                ·
                  refine ⟨6262999766239642987106357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4175333177493095324737571 6262999766239642987106357)
                  ·
                    refine ⟨587156228084966530041221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6262999766239642987106357 587156228084966530041221)
                    ·
                      rfl

theorem cell23_3430448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 5].length) (baseStart_3430448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430448 prefixEnd_3430448 := by exact prefixLift 3430448
  have htrace : WordTrace (prefixWord ++ tailWord_3430448) baseStart_3430448 baseEnd_3430448 := by
    simpa [prefixWord, tailWord_3430448, baseEnd_3430448] using wordTrace_append hprefix tailTrace_3430448
  have hstable : (prefixWord ++ tailWord_3430448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430448).length < 2 ^ (prefixWord ++ tailWord_3430448).sum := by decide
  have hdescent : baseEnd_3430448 < baseStart_3430448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430461 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_3430461 : Nat := 118140960795 + 3430461 * 2 ^ 59
def prefixEnd_3430461 : Nat := 4983230072969 + 3 ^ 40 * 3430461 * 2
def baseEnd_3430461 : Nat := 587158453167802679753701

theorem tailTrace_3430461 : CollatzResearch.WordTrace tailWord_3430461 prefixEnd_3430461 587158453167802679753701 := by
  unfold tailWord_3430461
  simp only [CollatzResearch.WordTrace]
  refine ⟨125119191625033147939931237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83412794416688765293287491 125119191625033147939931237)
  ·
    refine ⟨23459848429693715238737107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125119191625033147939931237 23459848429693715238737107)
    ·
      refine ⟨35189772644540572858105661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23459848429693715238737107 35189772644540572858105661)
      ·
        refine ⟨13196164741702714821789623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35189772644540572858105661 13196164741702714821789623)
        ·
          refine ⟨19794247112554072232684435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13196164741702714821789623 19794247112554072232684435)
          ·
            refine ⟨29691370668831108349026653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19794247112554072232684435 29691370668831108349026653)
            ·
              refine ⟨11134264000811665630884995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29691370668831108349026653 11134264000811665630884995)
              ·
                refine ⟨16701396001217498446327493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11134264000811665630884995 16701396001217498446327493)
                ·
                  refine ⟨3131511750228280958686405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16701396001217498446327493 3131511750228280958686405)
                  ·
                    refine ⟨587158453167802679753701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3131511750228280958686405 587158453167802679753701)
                    ·
                      rfl

theorem cell23_3430461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_3430461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430461 prefixEnd_3430461 := by exact prefixLift 3430461
  have htrace : WordTrace (prefixWord ++ tailWord_3430461) baseStart_3430461 baseEnd_3430461 := by
    simpa [prefixWord, tailWord_3430461, baseEnd_3430461] using wordTrace_append hprefix tailTrace_3430461
  have hstable : (prefixWord ++ tailWord_3430461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430461).length < 2 ^ (prefixWord ++ tailWord_3430461).sum := by decide
  have hdescent : baseEnd_3430461 < baseStart_3430461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430488 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 1, 2, 3]
def baseStart_3430488 : Nat := 118140960795 + 3430488 * 2 ^ 59
def prefixEnd_3430488 : Nat := 4983230072969 + 3 ^ 40 * 3430488 * 2
def baseEnd_3430488 : Nat := 1761489223481079433623479

theorem tailTrace_3430488 : CollatzResearch.WordTrace tailWord_3430488 prefixEnd_3430488 1761489223481079433623479 := by
  unfold tailWord_3430488
  simp only [CollatzResearch.WordTrace]
  refine ⟨62560088197967665775582059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83413450930623554367442745 62560088197967665775582059)
  ·
    refine ⟨93840132296951498663373089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62560088197967665775582059 93840132296951498663373089)
    ·
      refine ⟨70380099222713623997529817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93840132296951498663373089 70380099222713623997529817)
      ·
        refine ⟨52785074417035217998147363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70380099222713623997529817 52785074417035217998147363)
        ·
          refine ⟨79177611625552826997221045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52785074417035217998147363 79177611625552826997221045)
          ·
            refine ⟨7422901089895577530989473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79177611625552826997221045 7422901089895577530989473)
            ·
              refine ⟨5567175817421683148242105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7422901089895577530989473 5567175817421683148242105)
              ·
                refine ⟨4175381863066262361181579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5567175817421683148242105 4175381863066262361181579)
                ·
                  refine ⟨6263072794599393541772369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4175381863066262361181579 6263072794599393541772369)
                  ·
                    refine ⟨4697304595949545156329277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6263072794599393541772369 4697304595949545156329277)
                    ·
                      refine ⟨1761489223481079433623479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4697304595949545156329277 1761489223481079433623479)
                      ·
                        rfl

theorem cell23_3430488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_3430488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430488 prefixEnd_3430488 := by exact prefixLift 3430488
  have htrace : WordTrace (prefixWord ++ tailWord_3430488) baseStart_3430488 baseEnd_3430488 := by
    simpa [prefixWord, tailWord_3430488, baseEnd_3430488] using wordTrace_append hprefix tailTrace_3430488
  have hstable : (prefixWord ++ tailWord_3430488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430488).length < 2 ^ (prefixWord ++ tailWord_3430488).sum := by decide
  have hdescent : baseEnd_3430488 < baseStart_3430488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430535 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 2, 1, 3]
def baseStart_3430535 : Nat := 118140960795 + 3430535 * 2 ^ 59
def prefixEnd_3430535 : Nat := 4983230072969 + 3 ^ 40 * 3430535 * 2
def baseEnd_3430535 : Nat := 1761513357071840749735763

theorem tailTrace_3430535 : CollatzResearch.WordTrace tailWord_3430535 prefixEnd_3430535 1761513357071840749735763 := by
  unfold tailWord_3430535
  simp only [CollatzResearch.WordTrace]
  refine ⟨125121890626765058578125059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83414593751176705718750039 125121890626765058578125059)
  ·
    refine ⟨187682835940147587867187589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125121890626765058578125059 187682835940147587867187589)
    ·
      refine ⟨35190531738777672725097673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187682835940147587867187589 35190531738777672725097673)
      ·
        refine ⟨26392898804083254543823255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35190531738777672725097673 26392898804083254543823255)
        ·
          refine ⟨39589348206124881815734883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26392898804083254543823255 39589348206124881815734883)
          ·
            refine ⟨59384022309187322723602325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39589348206124881815734883 59384022309187322723602325)
            ·
              refine ⟨2783626045743155752668859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59384022309187322723602325 2783626045743155752668859)
              ·
                refine ⟨4175439068614733629003289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2783626045743155752668859 4175439068614733629003289)
                ·
                  refine ⟨3131579301461050221752467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4175439068614733629003289 3131579301461050221752467)
                  ·
                    refine ⟨4697368952191575332628701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3131579301461050221752467 4697368952191575332628701)
                    ·
                      refine ⟨1761513357071840749735763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4697368952191575332628701 1761513357071840749735763)
                      ·
                        rfl

theorem cell23_3430535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_3430535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430535 prefixEnd_3430535 := by exact prefixLift 3430535
  have htrace : WordTrace (prefixWord ++ tailWord_3430535) baseStart_3430535 baseEnd_3430535 := by
    simpa [prefixWord, tailWord_3430535, baseEnd_3430535] using wordTrace_append hprefix tailTrace_3430535
  have hstable : (prefixWord ++ tailWord_3430535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430535).length < 2 ^ (prefixWord ++ tailWord_3430535).sum := by decide
  have hdescent : baseEnd_3430535 < baseStart_3430535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430544 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 5]
def baseStart_3430544 : Nat := 118140960795 + 3430544 * 2 ^ 59
def prefixEnd_3430544 : Nat := 4983230072969 + 3 ^ 40 * 3430544 * 2
def baseEnd_3430544 : Nat := 1761517978397731214523221

theorem tailTrace_3430544 : CollatzResearch.WordTrace tailWord_3430544 prefixEnd_3430544 1761517978397731214523221 := by
  unfold tailWord_3430544
  simp only [CollatzResearch.WordTrace]
  refine ⟨62561109441866226557601343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83414812589154968743468457 62561109441866226557601343)
  ·
    refine ⟨93841664162799339836402015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62561109441866226557601343 93841664162799339836402015)
    ·
      refine ⟨140762496244199009754603023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93841664162799339836402015 140762496244199009754603023)
      ·
        refine ⟨211143744366298514631904535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140762496244199009754603023 211143744366298514631904535)
        ·
          refine ⟨316715616549447771947856803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211143744366298514631904535 316715616549447771947856803)
          ·
            refine ⟨475073424824171657921785205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316715616549447771947856803 475073424824171657921785205)
            ·
              refine ⟨44538133577266092930167363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 475073424824171657921785205 44538133577266092930167363)
              ·
                refine ⟨66807200365899139395251045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44538133577266092930167363 66807200365899139395251045)
                ·
                  refine ⟨12526350068606088636609571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66807200365899139395251045 12526350068606088636609571)
                  ·
                    refine ⟨18789525102909132954914357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12526350068606088636609571 18789525102909132954914357)
                    ·
                      refine ⟨1761517978397731214523221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18789525102909132954914357 1761517978397731214523221)
                      ·
                        rfl

theorem cell23_3430544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_3430544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430544 prefixEnd_3430544 := by exact prefixLift 3430544
  have htrace : WordTrace (prefixWord ++ tailWord_3430544) baseStart_3430544 baseEnd_3430544 := by
    simpa [prefixWord, tailWord_3430544, baseEnd_3430544] using wordTrace_append hprefix tailTrace_3430544
  have hstable : (prefixWord ++ tailWord_3430544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430544).length < 2 ^ (prefixWord ++ tailWord_3430544).sum := by decide
  have hdescent : baseEnd_3430544 < baseStart_3430544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430561 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3430561 : Nat := 118140960795 + 3430561 * 2 ^ 59
def prefixEnd_3430561 : Nat := 4983230072969 + 3 ^ 40 * 3430561 * 2
def baseEnd_3430561 : Nat := 1761526707568857648010643

theorem tailTrace_3430561 : CollatzResearch.WordTrace tailWord_3430561 prefixEnd_3430561 1761526707568857648010643 := by
  unfold tailWord_3430561
  simp only [CollatzResearch.WordTrace]
  refine ⟨125122838924670865018571537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83415225949780576679047691 125122838924670865018571537)
  ·
    refine ⟨93842129193503148763928653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125122838924670865018571537 93842129193503148763928653)
    ·
      refine ⟨35190798447563680786473245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93842129193503148763928653 35190798447563680786473245)
      ·
        refine ⟨13196549417836380294927467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35190798447563680786473245 13196549417836380294927467)
        ·
          refine ⟨19794824126754570442391201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13196549417836380294927467 19794824126754570442391201)
          ·
            refine ⟨14846118095065927831793401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19794824126754570442391201 14846118095065927831793401)
            ·
              refine ⟨11134588571299445873845051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14846118095065927831793401 11134588571299445873845051)
              ·
                refine ⟨16701882856949168810767577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11134588571299445873845051 16701882856949168810767577)
                ·
                  refine ⟨12526412142711876608075683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16701882856949168810767577 12526412142711876608075683)
                  ·
                    refine ⟨18789618214067814912113525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12526412142711876608075683 18789618214067814912113525)
                    ·
                      refine ⟨1761526707568857648010643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18789618214067814912113525 1761526707568857648010643)
                      ·
                        rfl

theorem cell23_3430561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3430561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430561 prefixEnd_3430561 := by exact prefixLift 3430561
  have htrace : WordTrace (prefixWord ++ tailWord_3430561) baseStart_3430561 baseEnd_3430561 := by
    simpa [prefixWord, tailWord_3430561, baseEnd_3430561] using wordTrace_append hprefix tailTrace_3430561
  have hstable : (prefixWord ++ tailWord_3430561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430561).length < 2 ^ (prefixWord ++ tailWord_3430561).sum := by decide
  have hdescent : baseEnd_3430561 < baseStart_3430561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430588 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_3430588 : Nat := 118140960795 + 3430588 * 2 ^ 59
def prefixEnd_3430588 : Nat := 4983230072969 + 3 ^ 40 * 3430588 * 2
def baseEnd_3430588 : Nat := 1761540571546529042373019

theorem tailTrace_3430588 : CollatzResearch.WordTrace tailWord_3430588 prefixEnd_3430588 1761540571546529042373019 := by
  unfold tailWord_3430588
  simp only [CollatzResearch.WordTrace]
  refine ⟨62561911847786524314902209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83415882463715365753202945 62561911847786524314902209)
  ·
    refine ⟨46921433885839893236176657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62561911847786524314902209 46921433885839893236176657)
    ·
      refine ⟨35191075414379919927132493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46921433885839893236176657 35191075414379919927132493)
      ·
        refine ⟨13196653280392469972674685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35191075414379919927132493 13196653280392469972674685)
        ·
          refine ⟨4948744980147176239753007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13196653280392469972674685 4948744980147176239753007)
          ·
            refine ⟨7423117470220764359629511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948744980147176239753007 7423117470220764359629511)
            ·
              refine ⟨11134676205331146539444267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7423117470220764359629511 11134676205331146539444267)
              ·
                refine ⟨16702014307996719809166401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11134676205331146539444267 16702014307996719809166401)
                ·
                  refine ⟨12526510730997539856874801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16702014307996719809166401 12526510730997539856874801)
                  ·
                    refine ⟨9394883048248154892656101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12526510730997539856874801 9394883048248154892656101)
                    ·
                      refine ⟨1761540571546529042373019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9394883048248154892656101 1761540571546529042373019)
                      ·
                        rfl

theorem cell23_3430588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_3430588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430588 prefixEnd_3430588 := by exact prefixLift 3430588
  have htrace : WordTrace (prefixWord ++ tailWord_3430588) baseStart_3430588 baseEnd_3430588 := by
    simpa [prefixWord, tailWord_3430588, baseEnd_3430588] using wordTrace_append hprefix tailTrace_3430588
  have hstable : (prefixWord ++ tailWord_3430588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430588).length < 2 ^ (prefixWord ++ tailWord_3430588).sum := by decide
  have hdescent : baseEnd_3430588 < baseStart_3430588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430626 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3430626 : Nat := 118140960795 + 3430626 * 2 ^ 59
def prefixEnd_3430626 : Nat := 4983230072969 + 3 ^ 40 * 3430626 * 2
def baseEnd_3430626 : Nat := 1761560083811399893697845

theorem tailTrace_3430626 : CollatzResearch.WordTrace tailWord_3430626 prefixEnd_3430626 1761560083811399893697845 := by
  unfold tailWord_3430626
  simp only [CollatzResearch.WordTrace]
  refine ⟨31281302417358845279921933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83416806446290254079791821 31281302417358845279921933)
  ·
    refine ⟨11730488406509566979970725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31281302417358845279921933 11730488406509566979970725)
    ·
      refine ⟨2199466576220543808744511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11730488406509566979970725 2199466576220543808744511)
      ·
        refine ⟨3299199864330815713116767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2199466576220543808744511 3299199864330815713116767)
        ·
          refine ⟨4948799796496223569675151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3299199864330815713116767 4948799796496223569675151)
          ·
            refine ⟨7423199694744335354512727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948799796496223569675151 7423199694744335354512727)
            ·
              refine ⟨11134799542116503031769091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7423199694744335354512727 11134799542116503031769091)
              ·
                refine ⟨16702199313174754547653637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11134799542116503031769091 16702199313174754547653637)
                ·
                  refine ⟨3131662371220266477685057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16702199313174754547653637 3131662371220266477685057)
                  ·
                    refine ⟨2348746778415199858263793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3131662371220266477685057 2348746778415199858263793)
                    ·
                      refine ⟨1761560083811399893697845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2348746778415199858263793 1761560083811399893697845)
                      ·
                        rfl

theorem cell23_3430626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3430626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430626 prefixEnd_3430626 := by exact prefixLift 3430626
  have htrace : WordTrace (prefixWord ++ tailWord_3430626) baseStart_3430626 baseEnd_3430626 := by
    simpa [prefixWord, tailWord_3430626, baseEnd_3430626] using wordTrace_append hprefix tailTrace_3430626
  have hstable : (prefixWord ++ tailWord_3430626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430626).length < 2 ^ (prefixWord ++ tailWord_3430626).sum := by decide
  have hdescent : baseEnd_3430626 < baseStart_3430626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430668 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 2, 2, 3]
def baseStart_3430668 : Nat := 118140960795 + 3430668 * 2 ^ 59
def prefixEnd_3430668 : Nat := 4983230072969 + 3 ^ 40 * 3430668 * 2
def baseEnd_3430668 : Nat := 1761581649998888729372651

theorem tailTrace_3430668 : CollatzResearch.WordTrace tailWord_3430668 prefixEnd_3430668 1761581649998888729372651 := by
  unfold tailWord_3430668
  simp only [CollatzResearch.WordTrace]
  refine ⟨62563370767641611146358329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83417827690188814861811105 62563370767641611146358329)
  ·
    refine ⟨46922528075731208359768747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62563370767641611146358329 46922528075731208359768747)
    ·
      refine ⟨70383792113596812539653121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46922528075731208359768747 70383792113596812539653121)
      ·
        refine ⟨52787844085197609404739841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70383792113596812539653121 52787844085197609404739841)
        ·
          refine ⟨39590883063898207053554881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52787844085197609404739841 39590883063898207053554881)
          ·
            refine ⟨29693162297923655290166161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39590883063898207053554881 29693162297923655290166161)
            ·
              refine ⟨22269871723442741467624621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29693162297923655290166161 22269871723442741467624621)
              ·
                refine ⟨8351201896291028050359233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22269871723442741467624621 8351201896291028050359233)
                ·
                  refine ⟨6263401422218271037769425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8351201896291028050359233 6263401422218271037769425)
                  ·
                    refine ⟨4697551066663703278327069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6263401422218271037769425 4697551066663703278327069)
                    ·
                      refine ⟨1761581649998888729372651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4697551066663703278327069 1761581649998888729372651)
                      ·
                        rfl

theorem cell23_3430668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_3430668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430668 prefixEnd_3430668 := by exact prefixLift 3430668
  have htrace : WordTrace (prefixWord ++ tailWord_3430668) baseStart_3430668 baseEnd_3430668 := by
    simpa [prefixWord, tailWord_3430668, baseEnd_3430668] using wordTrace_append hprefix tailTrace_3430668
  have hstable : (prefixWord ++ tailWord_3430668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430668).length < 2 ^ (prefixWord ++ tailWord_3430668).sum := by decide
  have hdescent : baseEnd_3430668 < baseStart_3430668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430732 : List Nat := [2, 2, 1, 3, 2, 1, 2, 5, 1, 1, 3]
def baseStart_3430732 : Nat := 118140960795 + 3430732 * 2 ^ 59
def prefixEnd_3430732 : Nat := 4983230072969 + 3 ^ 40 * 3430732 * 2
def baseEnd_3430732 : Nat := 1761614512760776478972357

theorem tailTrace_3430732 : CollatzResearch.WordTrace tailWord_3430732 prefixEnd_3430732 1761614512760776478972357 := by
  unfold tailWord_3430732
  simp only [CollatzResearch.WordTrace]
  refine ⟨62564537903525680611523225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83419383871367574148697633 62564537903525680611523225)
  ·
    refine ⟨46923403427644260458642419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62564537903525680611523225 46923403427644260458642419)
    ·
      refine ⟨70385105141466390687963629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46923403427644260458642419 70385105141466390687963629)
      ·
        refine ⟨26394414428049896507986361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70385105141466390687963629 26394414428049896507986361)
        ·
          refine ⟨19795810821037422380989771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26394414428049896507986361 19795810821037422380989771)
          ·
            refine ⟨29693716231556133571484657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19795810821037422380989771 29693716231556133571484657)
            ·
              refine ⟨22270287173667100178613493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29693716231556133571484657 22270287173667100178613493)
              ·
                refine ⟨2087839422531290641745015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22270287173667100178613493 2087839422531290641745015)
                ·
                  refine ⟨3131759133796935962617523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087839422531290641745015 3131759133796935962617523)
                  ·
                    refine ⟨4697638700695403943926285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3131759133796935962617523 4697638700695403943926285)
                    ·
                      refine ⟨1761614512760776478972357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4697638700695403943926285 1761614512760776478972357)
                      ·
                        rfl

theorem cell23_3430732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_3430732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430732 prefixEnd_3430732 := by exact prefixLift 3430732
  have htrace : WordTrace (prefixWord ++ tailWord_3430732) baseStart_3430732 baseEnd_3430732 := by
    simpa [prefixWord, tailWord_3430732, baseEnd_3430732] using wordTrace_append hprefix tailTrace_3430732
  have hstable : (prefixWord ++ tailWord_3430732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430732).length < 2 ^ (prefixWord ++ tailWord_3430732).sum := by decide
  have hdescent : baseEnd_3430732 < baseStart_3430732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430751 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_3430751 : Nat := 118140960795 + 3430751 * 2 ^ 59
def prefixEnd_3430751 : Nat := 4983230072969 + 3 ^ 40 * 3430751 * 2
def baseEnd_3430751 : Nat := 1761624268893211904634769

theorem tailTrace_3430751 : CollatzResearch.WordTrace tailWord_3430751 prefixEnd_3430751 1761624268893211904634769 := by
  unfold tailWord_3430751
  simp only [CollatzResearch.WordTrace]
  refine ⟨125129768793982527467988107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83419845862655018311992071 125129768793982527467988107)
  ·
    refine ⟨187694653190973791201982161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125129768793982527467988107 187694653190973791201982161)
    ·
      refine ⟨140770989893230343401486621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187694653190973791201982161 140770989893230343401486621)
      ·
        refine ⟨52789121209961378775557483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140770989893230343401486621 52789121209961378775557483)
        ·
          refine ⟨79183681814942068163336225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52789121209961378775557483 79183681814942068163336225)
          ·
            refine ⟨59387761361206551122502169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79183681814942068163336225 59387761361206551122502169)
            ·
              refine ⟨44540821020904913341876627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59387761361206551122502169 44540821020904913341876627)
              ·
                refine ⟨66811231531357370012814941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44540821020904913341876627 66811231531357370012814941)
                ·
                  refine ⟨25054211824259013754805603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66811231531357370012814941 25054211824259013754805603)
                  ·
                    refine ⟨37581317736388520632208405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25054211824259013754805603 37581317736388520632208405)
                    ·
                      refine ⟨1761624268893211904634769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37581317736388520632208405 1761624268893211904634769)
                      ·
                        rfl

theorem cell23_3430751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_3430751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430751 prefixEnd_3430751 := by exact prefixLift 3430751
  have htrace : WordTrace (prefixWord ++ tailWord_3430751) baseStart_3430751 baseEnd_3430751 := by
    simpa [prefixWord, tailWord_3430751, baseEnd_3430751] using wordTrace_append hprefix tailTrace_3430751
  have hstable : (prefixWord ++ tailWord_3430751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430751).length < 2 ^ (prefixWord ++ tailWord_3430751).sum := by decide
  have hdescent : baseEnd_3430751 < baseStart_3430751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430765 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_3430765 : Nat := 118140960795 + 3430765 * 2 ^ 59
def prefixEnd_3430765 : Nat := 4983230072969 + 3 ^ 40 * 3430765 * 2
def baseEnd_3430765 : Nat := 587210485874124949953235

theorem tailTrace_3430765 : CollatzResearch.WordTrace tailWord_3430765 prefixEnd_3430765 587210485874124949953235 := by
  unfold tailWord_3430765
  simp only [CollatzResearch.WordTrace]
  refine ⟨125130279415931807858997749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83420186277287871905998499 125130279415931807858997749)
  ·
    refine ⟨11730963695243606986781039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125130279415931807858997749 11730963695243606986781039)
    ·
      refine ⟨17596445542865410480171559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11730963695243606986781039 17596445542865410480171559)
      ·
        refine ⟨26394668314298115720257339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17596445542865410480171559 26394668314298115720257339)
        ·
          refine ⟨39592002471447173580386009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26394668314298115720257339 39592002471447173580386009)
          ·
            refine ⟨29694001853585380185289507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39592002471447173580386009 29694001853585380185289507)
            ·
              refine ⟨44541002780378070277934261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29694001853585380185289507 44541002780378070277934261)
              ·
                refine ⟨4175719010660444088556337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44541002780378070277934261 4175719010660444088556337)
                ·
                  refine ⟨3131789257995333066417253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4175719010660444088556337 3131789257995333066417253)
                  ·
                    refine ⟨587210485874124949953235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3131789257995333066417253 587210485874124949953235)
                    ·
                      rfl

theorem cell23_3430765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_3430765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430765 prefixEnd_3430765 := by exact prefixLift 3430765
  have htrace : WordTrace (prefixWord ++ tailWord_3430765) baseStart_3430765 baseEnd_3430765 := by
    simpa [prefixWord, tailWord_3430765, baseEnd_3430765] using wordTrace_append hprefix tailTrace_3430765
  have hstable : (prefixWord ++ tailWord_3430765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430765).length < 2 ^ (prefixWord ++ tailWord_3430765).sum := by decide
  have hdescent : baseEnd_3430765 < baseStart_3430765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430768 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 4]
def baseStart_3430768 : Nat := 118140960795 + 3430768 * 2 ^ 59
def prefixEnd_3430768 : Nat := 4983230072969 + 3 ^ 40 * 3430768 * 2
def baseEnd_3430768 : Nat := 1761632998064338338122191

theorem tailTrace_3430768 : CollatzResearch.WordTrace tailWord_3430768 prefixEnd_3430768 1761632998064338338122191 := by
  unfold tailWord_3430768
  simp only [CollatzResearch.WordTrace]
  refine ⟨62565194417460469685678479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83420259223280626247571305 62565194417460469685678479)
  ·
    refine ⟨93847791626190704528517719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62565194417460469685678479 93847791626190704528517719)
    ·
      refine ⟨140771687439286056792776579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93847791626190704528517719 140771687439286056792776579)
      ·
        refine ⟨211157531158929085189164869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140771687439286056792776579 211157531158929085189164869)
        ·
          refine ⟨39592037092299203472968413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211157531158929085189164869 39592037092299203472968413)
          ·
            refine ⟨14847013909612201302363155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39592037092299203472968413 14847013909612201302363155)
            ·
              refine ⟨22270520864418301953544733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14847013909612201302363155 22270520864418301953544733)
              ·
                refine ⟨8351445324156863232579275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22270520864418301953544733 8351445324156863232579275)
                ·
                  refine ⟨12527167986235294848868913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8351445324156863232579275 12527167986235294848868913)
                  ·
                    refine ⟨9395375989676471136651685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12527167986235294848868913 9395375989676471136651685)
                    ·
                      refine ⟨1761632998064338338122191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9395375989676471136651685 1761632998064338338122191)
                      ·
                        rfl

theorem cell23_3430768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_3430768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430768 prefixEnd_3430768 := by exact prefixLift 3430768
  have htrace : WordTrace (prefixWord ++ tailWord_3430768) baseStart_3430768 baseEnd_3430768 := by
    simpa [prefixWord, tailWord_3430768, baseEnd_3430768] using wordTrace_append hprefix tailTrace_3430768
  have hstable : (prefixWord ++ tailWord_3430768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430768).length < 2 ^ (prefixWord ++ tailWord_3430768).sum := by decide
  have hdescent : baseEnd_3430768 < baseStart_3430768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430785 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3430785 : Nat := 118140960795 + 3430785 * 2 ^ 59
def prefixEnd_3430785 : Nat := 4983230072969 + 3 ^ 40 * 3430785 * 2
def baseEnd_3430785 : Nat := 1761641727235464771609613

theorem tailTrace_3430785 : CollatzResearch.WordTrace tailWord_3430785 prefixEnd_3430785 1761641727235464771609613 := by
  unfold tailWord_3430785
  simp only [CollatzResearch.WordTrace]
  refine ⟨125131008875859351274725809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83420672583906234183150539 125131008875859351274725809)
  ·
    refine ⟨93848256656894513456044357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125131008875859351274725809 93848256656894513456044357)
    ·
      refine ⟨17596548123167721273008317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93848256656894513456044357 17596548123167721273008317)
      ·
        refine ⟨6598705546187895477378119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17596548123167721273008317 6598705546187895477378119)
        ·
          refine ⟨9898058319281843216067179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6598705546187895477378119 9898058319281843216067179)
          ·
            refine ⟨14847087478922764824100769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9898058319281843216067179 14847087478922764824100769)
            ·
              refine ⟨11135315609192073618075577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14847087478922764824100769 11135315609192073618075577)
              ·
                refine ⟨8351486706894055213556683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11135315609192073618075577 8351486706894055213556683)
                ·
                  refine ⟨12527230060341082820335025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8351486706894055213556683 12527230060341082820335025)
                  ·
                    refine ⟨9395422545255812115251269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12527230060341082820335025 9395422545255812115251269)
                    ·
                      refine ⟨1761641727235464771609613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9395422545255812115251269 1761641727235464771609613)
                      ·
                        rfl

theorem cell23_3430785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3430785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430785 prefixEnd_3430785 := by exact prefixLift 3430785
  have htrace : WordTrace (prefixWord ++ tailWord_3430785) baseStart_3430785 baseEnd_3430785 := by
    simpa [prefixWord, tailWord_3430785, baseEnd_3430785] using wordTrace_append hprefix tailTrace_3430785
  have hstable : (prefixWord ++ tailWord_3430785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430785).length < 2 ^ (prefixWord ++ tailWord_3430785).sum := by decide
  have hdescent : baseEnd_3430785 < baseStart_3430785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430786 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3430786 : Nat := 118140960795 + 3430786 * 2 ^ 59
def prefixEnd_3430786 : Nat := 4983230072969 + 3 ^ 40 * 3430786 * 2
def baseEnd_3430786 : Nat := 587214080238706422565703

theorem tailTrace_3430786 : CollatzResearch.WordTrace tailWord_3430786 prefixEnd_3430786 587214080238706422565703 := by
  unfold tailWord_3430786
  simp only [CollatzResearch.WordTrace]
  refine ⟨31282761337213932111378053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83420696899237152297008141 31282761337213932111378053)
  ·
    refine ⟨5865517750727612270883385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31282761337213932111378053 5865517750727612270883385)
    ·
      refine ⟨4399138313045709203162539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5865517750727612270883385 4399138313045709203162539)
      ·
        refine ⟨6598707469568563804743809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4399138313045709203162539 6598707469568563804743809)
        ·
          refine ⟨4949030602176422853557857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6598707469568563804743809 4949030602176422853557857)
          ·
            refine ⟨3711772951632317140168393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4949030602176422853557857 3711772951632317140168393)
            ·
              refine ⟨2783829713724237855126295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3711772951632317140168393 2783829713724237855126295)
              ·
                refine ⟨4175744570586356782689443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2783829713724237855126295 4175744570586356782689443)
                ·
                  refine ⟨6263616855879535174034165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4175744570586356782689443 6263616855879535174034165)
                  ·
                    refine ⟨587214080238706422565703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6263616855879535174034165 587214080238706422565703)
                    ·
                      rfl

theorem cell23_3430786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3430786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430786 prefixEnd_3430786 := by exact prefixLift 3430786
  have htrace : WordTrace (prefixWord ++ tailWord_3430786) baseStart_3430786 baseEnd_3430786 := by
    simpa [prefixWord, tailWord_3430786, baseEnd_3430786] using wordTrace_append hprefix tailTrace_3430786
  have hstable : (prefixWord ++ tailWord_3430786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430786).length < 2 ^ (prefixWord ++ tailWord_3430786).sum := by decide
  have hdescent : baseEnd_3430786 < baseStart_3430786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430801 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_3430801 : Nat := 118140960795 + 3430801 * 2 ^ 59
def prefixEnd_3430801 : Nat := 4983230072969 + 3 ^ 40 * 3430801 * 2
def baseEnd_3430801 : Nat := 1761649942925936709009539

theorem tailTrace_3430801 : CollatzResearch.WordTrace tailWord_3430801 prefixEnd_3430801 1761649942925936709009539 := by
  unfold tailWord_3430801
  simp only [CollatzResearch.WordTrace]
  refine ⟨125131592443801386007308257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83421061629200924004872171 125131592443801386007308257)
  ·
    refine ⟨93848694332851039505481193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125131592443801386007308257 93848694332851039505481193)
    ·
      refine ⟨70386520749638279629110895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93848694332851039505481193 70386520749638279629110895)
      ·
        refine ⟨105579781124457419443666343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70386520749638279629110895 105579781124457419443666343)
        ·
          refine ⟨158369671686686129165499515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105579781124457419443666343 158369671686686129165499515)
          ·
            refine ⟨237554507530029193748249273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158369671686686129165499515 237554507530029193748249273)
            ·
              refine ⟨178165880647521895311186955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237554507530029193748249273 178165880647521895311186955)
              ·
                refine ⟨267248820971282842966780433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178165880647521895311186955 267248820971282842966780433)
                ·
                  refine ⟨200436615728462132225085325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267248820971282842966780433 200436615728462132225085325)
                  ·
                    refine ⟨75163730898173299584406997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200436615728462132225085325 75163730898173299584406997)
                    ·
                      refine ⟨1761649942925936709009539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75163730898173299584406997 1761649942925936709009539)
                      ·
                        rfl

theorem cell23_3430801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_3430801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430801 prefixEnd_3430801 := by exact prefixLift 3430801
  have htrace : WordTrace (prefixWord ++ tailWord_3430801) baseStart_3430801 baseEnd_3430801 := by
    simpa [prefixWord, tailWord_3430801, baseEnd_3430801] using wordTrace_append hprefix tailTrace_3430801
  have hstable : (prefixWord ++ tailWord_3430801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430801).length < 2 ^ (prefixWord ++ tailWord_3430801).sum := by decide
  have hdescent : baseEnd_3430801 < baseStart_3430801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430829 : List Nat := [1, 5, 2, 2, 3, 1, 2, 7]
def baseStart_3430829 : Nat := 118140960795 + 3430829 * 2 ^ 59
def prefixEnd_3430829 : Nat := 4983230072969 + 3 ^ 40 * 3430829 * 2
def baseEnd_3430829 : Nat := 65246826680898614794793

theorem tailTrace_3430829 : CollatzResearch.WordTrace tailWord_3430829 prefixEnd_3430829 65246826680898614794793 := by
  unfold tailWord_3430829
  simp only [CollatzResearch.WordTrace]
  refine ⟨125132613687699946789327541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83421742458466631192885027 125132613687699946789327541)
  ·
    refine ⟨11731182533221870011499457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125132613687699946789327541 11731182533221870011499457)
    ·
      refine ⟨8798386899916402508624593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11731182533221870011499457 8798386899916402508624593)
      ·
        refine ⟨6598790174937301881468445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8798386899916402508624593 6598790174937301881468445)
        ·
          refine ⟨2474546315601488205550667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6598790174937301881468445 2474546315601488205550667)
          ·
            refine ⟨3711819473402232308326001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474546315601488205550667 3711819473402232308326001)
            ·
              refine ⟨2783864605051674231244501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3711819473402232308326001 2783864605051674231244501)
              ·
                refine ⟨65246826680898614794793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2783864605051674231244501 65246826680898614794793)
                ·
                  rfl

theorem cell23_3430829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 7].length) (baseStart_3430829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430829 prefixEnd_3430829 := by exact prefixLift 3430829
  have htrace : WordTrace (prefixWord ++ tailWord_3430829) baseStart_3430829 baseEnd_3430829 := by
    simpa [prefixWord, tailWord_3430829, baseEnd_3430829] using wordTrace_append hprefix tailTrace_3430829
  have hstable : (prefixWord ++ tailWord_3430829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430829).length < 2 ^ (prefixWord ++ tailWord_3430829).sum := by decide
  have hdescent : baseEnd_3430829 < baseStart_3430829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430848 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 3]
def baseStart_3430848 : Nat := 118140960795 + 3430848 * 2 ^ 59
def prefixEnd_3430848 : Nat := 4983230072969 + 3 ^ 40 * 3430848 * 2
def baseEnd_3430848 : Nat := 1761674076516698025121823

theorem tailTrace_3430848 : CollatzResearch.WordTrace tailWord_3430848 prefixEnd_3430848 1761674076516698025121823 := by
  unfold tailWord_3430848
  simp only [CollatzResearch.WordTrace]
  refine ⟨62566653337315556517134599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83422204449754075356179465 62566653337315556517134599)
  ·
    refine ⟨93849980005973334775701899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62566653337315556517134599 93849980005973334775701899)
    ·
      refine ⟨140774970008960002163552849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93849980005973334775701899 140774970008960002163552849)
      ·
        refine ⟨105581227506720001622664637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140774970008960002163552849 105581227506720001622664637)
        ·
          refine ⟨39592960315020000608499239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105581227506720001622664637 39592960315020000608499239)
          ·
            refine ⟨59389440472530000912748859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39592960315020000608499239 59389440472530000912748859)
            ·
              refine ⟨89084160708795001369123289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59389440472530000912748859 89084160708795001369123289)
              ·
                refine ⟨66813120531596251026842467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89084160708795001369123289 66813120531596251026842467)
                ·
                  refine ⟨100219680797394376540263701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66813120531596251026842467 100219680797394376540263701)
                  ·
                    refine ⟨4697797537377861400324861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100219680797394376540263701 4697797537377861400324861)
                    ·
                      refine ⟨1761674076516698025121823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4697797537377861400324861 1761674076516698025121823)
                      ·
                        rfl

theorem cell23_3430848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_3430848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430848 prefixEnd_3430848 := by exact prefixLift 3430848
  have htrace : WordTrace (prefixWord ++ tailWord_3430848) baseStart_3430848 baseEnd_3430848 := by
    simpa [prefixWord, tailWord_3430848, baseEnd_3430848] using wordTrace_append hprefix tailTrace_3430848
  have hstable : (prefixWord ++ tailWord_3430848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430848).length < 2 ^ (prefixWord ++ tailWord_3430848).sum := by decide
  have hdescent : baseEnd_3430848 < baseStart_3430848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430879 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 2, 2, 2]
def baseStart_3430879 : Nat := 118140960795 + 3430879 * 2 ^ 59
def prefixEnd_3430879 : Nat := 4983230072969 + 3 ^ 40 * 3430879 * 2
def baseEnd_3430879 : Nat := 1761689994416987403834181

theorem tailTrace_3430879 : CollatzResearch.WordTrace tailWord_3430879 prefixEnd_3430879 1761689994416987403834181 := by
  unfold tailWord_3430879
  simp only [CollatzResearch.WordTrace]
  refine ⟨125134437337518805328647691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83422958225012536885765127 125134437337518805328647691)
  ·
    refine ⟨187701656006278207992971537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125134437337518805328647691 187701656006278207992971537)
    ·
      refine ⟨140776242004708655994728653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187701656006278207992971537 140776242004708655994728653)
      ·
        refine ⟨52791090751765745998023245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140776242004708655994728653 52791090751765745998023245)
        ·
          refine ⟨19796659031912154749258717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52791090751765745998023245 19796659031912154749258717)
          ·
            refine ⟨7423747136967058030972019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19796659031912154749258717 7423747136967058030972019)
            ·
              refine ⟨11135620705450587046458029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7423747136967058030972019 11135620705450587046458029)
              ·
                refine ⟨4175857764543970142421761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11135620705450587046458029 4175857764543970142421761)
                ·
                  refine ⟨3131893323407977606816321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4175857764543970142421761 3131893323407977606816321)
                  ·
                    refine ⟨2348919992555983205112241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3131893323407977606816321 2348919992555983205112241)
                    ·
                      refine ⟨1761689994416987403834181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2348919992555983205112241 1761689994416987403834181)
                      ·
                        rfl

theorem cell23_3430879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_3430879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430879 prefixEnd_3430879 := by exact prefixLift 3430879
  have htrace : WordTrace (prefixWord ++ tailWord_3430879) baseStart_3430879 baseEnd_3430879 := by
    simpa [prefixWord, tailWord_3430879, baseEnd_3430879] using wordTrace_append hprefix tailTrace_3430879
  have hstable : (prefixWord ++ tailWord_3430879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430879).length < 2 ^ (prefixWord ++ tailWord_3430879).sum := by decide
  have hdescent : baseEnd_3430879 < baseStart_3430879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430902 : List Nat := [5, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_3430902 : Nat := 118140960795 + 3430902 * 2 ^ 59
def prefixEnd_3430902 : Nat := 4983230072969 + 3 ^ 40 * 3430902 * 2
def baseEnd_3430902 : Nat := 195744644941337868205175

theorem tailTrace_3430902 : CollatzResearch.WordTrace tailWord_3430902 prefixEnd_3430902 195744644941337868205175 := by
  unfold tailWord_3430902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7820954763527217516045935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83423517477623653504489973 7820954763527217516045935)
  ·
    refine ⟨11731432145290826274068903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7820954763527217516045935 11731432145290826274068903)
    ·
      refine ⟨17597148217936239411103355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11731432145290826274068903 17597148217936239411103355)
      ·
        refine ⟨26395722326904359116655033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17597148217936239411103355 26395722326904359116655033)
        ·
          refine ⟨19796791745178269337491275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26395722326904359116655033 19796791745178269337491275)
          ·
            refine ⟨29695187617767404006236913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19796791745178269337491275 29695187617767404006236913)
            ·
              refine ⟨22271390713325553004677685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29695187617767404006236913 22271390713325553004677685)
              ·
                refine ⟨2087942879374270594188533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22271390713325553004677685 2087942879374270594188533)
                ·
                  refine ⟨195744644941337868205175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2087942879374270594188533 195744644941337868205175)
                  ·
                    rfl

theorem cell23_3430902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_3430902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430902 prefixEnd_3430902 := by exact prefixLift 3430902
  have htrace : WordTrace (prefixWord ++ tailWord_3430902) baseStart_3430902 baseEnd_3430902 := by
    simpa [prefixWord, tailWord_3430902, baseEnd_3430902] using wordTrace_append hprefix tailTrace_3430902
  have hstable : (prefixWord ++ tailWord_3430902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430902).length < 2 ^ (prefixWord ++ tailWord_3430902).sum := by decide
  have hdescent : baseEnd_3430902 < baseStart_3430902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430952 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3430952 : Nat := 118140960795 + 3430952 * 2 ^ 59
def prefixEnd_3430952 : Nat := 4983230072969 + 3 ^ 40 * 3430952 * 2
def baseEnd_3430952 : Nat := 1761727478504765618221345

theorem tailTrace_3430952 : CollatzResearch.WordTrace tailWord_3430952 prefixEnd_3430952 1761727478504765618221345 := by
  unfold tailWord_3430952
  simp only [CollatzResearch.WordTrace]
  refine ⟨62568549933127169398027555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83424733244169559197370073 62568549933127169398027555)
  ·
    refine ⟨93852824899690754097041333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62568549933127169398027555 93852824899690754097041333)
    ·
      refine ⟨8798702334346008196597625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93852824899690754097041333 8798702334346008196597625)
      ·
        refine ⟨6599026750759506147448219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8798702334346008196597625 6599026750759506147448219)
        ·
          refine ⟨9898540126139259221172329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6599026750759506147448219 9898540126139259221172329)
          ·
            refine ⟨7423905094604444415879247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9898540126139259221172329 7423905094604444415879247)
            ·
              refine ⟨11135857641906666623818871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7423905094604444415879247 11135857641906666623818871)
              ·
                refine ⟨16703786462859999935728307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11135857641906666623818871 16703786462859999935728307)
                ·
                  refine ⟨25055679694289999903592461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16703786462859999935728307 25055679694289999903592461)
                  ·
                    refine ⟨9395879885358749963847173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25055679694289999903592461 9395879885358749963847173)
                    ·
                      refine ⟨1761727478504765618221345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9395879885358749963847173 1761727478504765618221345)
                      ·
                        rfl

theorem cell23_3430952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3430952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3430952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3430952 prefixEnd_3430952 := by exact prefixLift 3430952
  have htrace : WordTrace (prefixWord ++ tailWord_3430952) baseStart_3430952 baseEnd_3430952 := by
    simpa [prefixWord, tailWord_3430952, baseEnd_3430952] using wordTrace_append hprefix tailTrace_3430952
  have hstable : (prefixWord ++ tailWord_3430952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430952).length < 2 ^ (prefixWord ++ tailWord_3430952).sum := by decide
  have hdescent : baseEnd_3430952 < baseStart_3430952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431012 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 1, 5, 2]
def baseStart_3431012 : Nat := 118140960795 + 3431012 * 2 ^ 59
def prefixEnd_3431012 : Nat := 4983230072969 + 3 ^ 40 * 3431012 * 2
def baseEnd_3431012 : Nat := 1761758287344035383471069

theorem tailTrace_3431012 : CollatzResearch.WordTrace tailWord_3431012 prefixEnd_3431012 1761758287344035383471069 := by
  unfold tailWord_3431012
  simp only [CollatzResearch.WordTrace]
  refine ⟨62569644123018484521619645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83426192164024646028826193 62569644123018484521619645)
  ·
    refine ⟨23463616546131931695607367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62569644123018484521619645 23463616546131931695607367)
    ·
      refine ⟨35195424819197897543411051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23463616546131931695607367 35195424819197897543411051)
      ·
        refine ⟨52793137228796846315116577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35195424819197897543411051 52793137228796846315116577)
        ·
          refine ⟨39594852921597634736337433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52793137228796846315116577 39594852921597634736337433)
          ·
            refine ⟨29696139691198226052253075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39594852921597634736337433 29696139691198226052253075)
            ·
              refine ⟨44544209536797339078379613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29696139691198226052253075 44544209536797339078379613)
              ·
                refine ⟨16704078576299002154392355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44544209536797339078379613 16704078576299002154392355)
                ·
                  refine ⟨25056117864448503231588533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16704078576299002154392355 25056117864448503231588533)
                  ·
                    refine ⟨2349011049792047177961425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25056117864448503231588533 2349011049792047177961425)
                    ·
                      refine ⟨1761758287344035383471069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349011049792047177961425 1761758287344035383471069)
                      ·
                        rfl

theorem cell23_3431012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_3431012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431012 prefixEnd_3431012 := by exact prefixLift 3431012
  have htrace : WordTrace (prefixWord ++ tailWord_3431012) baseStart_3431012 baseEnd_3431012 := by
    simpa [prefixWord, tailWord_3431012, baseEnd_3431012] using wordTrace_append hprefix tailTrace_3431012
  have hstable : (prefixWord ++ tailWord_3431012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431012).length < 2 ^ (prefixWord ++ tailWord_3431012).sum := by decide
  have hdescent : baseEnd_3431012 < baseStart_3431012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431013 : List Nat := [1, 3, 1, 3, 5, 1, 1, 3, 1, 4]
def baseStart_3431013 : Nat := 118140960795 + 3431013 * 2 ^ 59
def prefixEnd_3431013 : Nat := 4983230072969 + 3 ^ 40 * 3431013 * 2
def baseEnd_3431013 : Nat := 587252933608229959852855

theorem tailTrace_3431013 : CollatzResearch.WordTrace tailWord_3431013 prefixEnd_3431013 587252933608229959852855 := by
  unfold tailWord_3431013
  simp only [CollatzResearch.WordTrace]
  refine ⟨125139324719033346214025693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83426216479355564142683795 125139324719033346214025693)
  ·
    refine ⟨46927246769637504830259635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125139324719033346214025693 46927246769637504830259635)
    ·
      refine ⟨70390870154456257245389453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46927246769637504830259635 70390870154456257245389453)
      ·
        refine ⟨26396576307921096467021045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70390870154456257245389453 26396576307921096467021045)
        ·
          refine ⟨2474679028867602793783223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26396576307921096467021045 2474679028867602793783223)
          ·
            refine ⟨3712018543301404190674835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474679028867602793783223 3712018543301404190674835)
            ·
              refine ⟨5568027814952106286012253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712018543301404190674835 5568027814952106286012253)
              ·
                refine ⟨2088010430607039857254595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5568027814952106286012253 2088010430607039857254595)
                ·
                  refine ⟨3132015645910559785881893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088010430607039857254595 3132015645910559785881893)
                  ·
                    refine ⟨587252933608229959852855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3132015645910559785881893 587252933608229959852855)
                    ·
                      rfl

theorem cell23_3431013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_3431013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431013 prefixEnd_3431013 := by exact prefixLift 3431013
  have htrace : WordTrace (prefixWord ++ tailWord_3431013) baseStart_3431013 baseEnd_3431013 := by
    simpa [prefixWord, tailWord_3431013, baseEnd_3431013] using wordTrace_append hprefix tailTrace_3431013
  have hstable : (prefixWord ++ tailWord_3431013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431013).length < 2 ^ (prefixWord ++ tailWord_3431013).sum := by decide
  have hdescent : baseEnd_3431013 < baseStart_3431013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431019 : List Nat := [1, 1, 1, 1, 2, 2, 1, 9, 1, 1, 3]
def baseStart_3431019 : Nat := 118140960795 + 3431019 * 2 ^ 59
def prefixEnd_3431019 : Nat := 4983230072969 + 3 ^ 40 * 3431019 * 2
def baseEnd_3431019 : Nat := 1761761881708616856083537

theorem tailTrace_3431019 : CollatzResearch.WordTrace tailWord_3431019 prefixEnd_3431019 1761761881708616856083537 := by
  unfold tailWord_3431019
  simp only [CollatzResearch.WordTrace]
  refine ⟨125139543557011609238744111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83426362371341072825829407 125139543557011609238744111)
  ·
    refine ⟨187709315335517413858116167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125139543557011609238744111 187709315335517413858116167)
    ·
      refine ⟨281563973003276120787174251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187709315335517413858116167 281563973003276120787174251)
      ·
        refine ⟨422345959504914181180761377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281563973003276120787174251 422345959504914181180761377)
        ·
          refine ⟨316759469628685635885571033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422345959504914181180761377 316759469628685635885571033)
          ·
            refine ⟨237569602221514226914178275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316759469628685635885571033 237569602221514226914178275)
            ·
              refine ⟨356354403332271340371267413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237569602221514226914178275 356354403332271340371267413)
              ·
                refine ⟨2088014082025027384987895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 356354403332271340371267413 2088014082025027384987895)
                ·
                  refine ⟨3132021123037541077481843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088014082025027384987895 3132021123037541077481843)
                  ·
                    refine ⟨4698031684556311616222765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3132021123037541077481843 4698031684556311616222765)
                    ·
                      refine ⟨1761761881708616856083537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4698031684556311616222765 1761761881708616856083537)
                      ·
                        rfl

theorem cell23_3431019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 1, 1, 3].length) (baseStart_3431019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431019 prefixEnd_3431019 := by exact prefixLift 3431019
  have htrace : WordTrace (prefixWord ++ tailWord_3431019) baseStart_3431019 baseEnd_3431019 := by
    simpa [prefixWord, tailWord_3431019, baseEnd_3431019] using wordTrace_append hprefix tailTrace_3431019
  have hstable : (prefixWord ++ tailWord_3431019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431019).length < 2 ^ (prefixWord ++ tailWord_3431019).sum := by decide
  have hdescent : baseEnd_3431019 < baseStart_3431019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431025 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_3431025 : Nat := 118140960795 + 3431025 * 2 ^ 59
def prefixEnd_3431025 : Nat := 4983230072969 + 3 ^ 40 * 3431025 * 2
def baseEnd_3431025 : Nat := 1761764962592543832608509

theorem tailTrace_3431025 : CollatzResearch.WordTrace tailWord_3431025 prefixEnd_3431025 1761764962592543832608509 := by
  unfold tailWord_3431025
  simp only [CollatzResearch.WordTrace]
  refine ⟨125139762394989872263462529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83426508263326581508975019 125139762394989872263462529)
  ·
    refine ⟨93854821796242404197596897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125139762394989872263462529 93854821796242404197596897)
    ·
      refine ⟨70391116347181803148197673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93854821796242404197596897 70391116347181803148197673)
      ·
        refine ⟨52793337260386352361148255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70391116347181803148197673 52793337260386352361148255)
        ·
          refine ⟨79190005890579528541722383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52793337260386352361148255 79190005890579528541722383)
          ·
            refine ⟨118785008835869292812583575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79190005890579528541722383 118785008835869292812583575)
            ·
              refine ⟨178177513253803939218875363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118785008835869292812583575 178177513253803939218875363)
              ·
                refine ⟨267266269880705908828313045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178177513253803939218875363 267266269880705908828313045)
                ·
                  refine ⟨6264053200329044738163587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 267266269880705908828313045 6264053200329044738163587)
                  ·
                    refine ⟨9396079800493567107245381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6264053200329044738163587 9396079800493567107245381)
                    ·
                      refine ⟨1761764962592543832608509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9396079800493567107245381 1761764962592543832608509)
                      ·
                        rfl

theorem cell23_3431025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_3431025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431025 prefixEnd_3431025 := by exact prefixLift 3431025
  have htrace : WordTrace (prefixWord ++ tailWord_3431025) baseStart_3431025 baseEnd_3431025 := by
    simpa [prefixWord, tailWord_3431025, baseEnd_3431025] using wordTrace_append hprefix tailTrace_3431025
  have hstable : (prefixWord ++ tailWord_3431025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431025).length < 2 ^ (prefixWord ++ tailWord_3431025).sum := by decide
  have hdescent : baseEnd_3431025 < baseStart_3431025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431082 : List Nat := [3, 1, 5, 2, 12]
def baseStart_3431082 : Nat := 118140960795 + 3431082 * 2 ^ 59
def prefixEnd_3431082 : Nat := 4983230072969 + 3 ^ 40 * 3431082 * 2
def baseEnd_3431082 : Nat := 2416727340178120863643

theorem tailTrace_3431082 : CollatzResearch.WordTrace tailWord_3431082 prefixEnd_3431082 2416727340178120863643 := by
  unfold tailWord_3431082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31285460338945842749571875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83427894237188913998858333 31285460338945842749571875)
  ·
    refine ⟨46928190508418764124357813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31285460338945842749571875 46928190508418764124357813)
    ·
      refine ⟨4399517860164259136658545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46928190508418764124357813 4399517860164259136658545)
      ·
        refine ⟨3299638395123194352493909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4399517860164259136658545 3299638395123194352493909)
        ·
          refine ⟨2416727340178120863643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3299638395123194352493909 2416727340178120863643)
          ·
            rfl

theorem cell23_3431082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 12].length) (baseStart_3431082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431082 prefixEnd_3431082 := by exact prefixLift 3431082
  have htrace : WordTrace (prefixWord ++ tailWord_3431082) baseStart_3431082 baseEnd_3431082 := by
    simpa [prefixWord, tailWord_3431082, baseEnd_3431082] using wordTrace_append hprefix tailTrace_3431082
  have hstable : (prefixWord ++ tailWord_3431082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431082).length < 2 ^ (prefixWord ++ tailWord_3431082).sum := by decide
  have hdescent : baseEnd_3431082 < baseStart_3431082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431086 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3431086 : Nat := 118140960795 + 3431086 * 2 ^ 59
def prefixEnd_3431086 : Nat := 4983230072969 + 3 ^ 40 * 3431086 * 2
def baseEnd_3431086 : Nat := 587265428304156031315243

theorem tailTrace_3431086 : CollatzResearch.WordTrace tailWord_3431086 prefixEnd_3431086 587265428304156031315243 := by
  unfold tailWord_3431086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15642748405971109960179139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83427991498512586454288741 15642748405971109960179139)
  ·
    refine ⟨23464122608956664940268709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15642748405971109960179139 23464122608956664940268709)
    ·
      refine ⟨4399522989179374676300383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23464122608956664940268709 4399522989179374676300383)
      ·
        refine ⟨6599284483769062014450575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4399522989179374676300383 6599284483769062014450575)
        ·
          refine ⟨9898926725653593021675863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6599284483769062014450575 9898926725653593021675863)
          ·
            refine ⟨14848390088480389532513795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9898926725653593021675863 14848390088480389532513795)
            ·
              refine ⟨22272585132720584298770693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14848390088480389532513795 22272585132720584298770693)
              ·
                refine ⟨4176109712385109556019505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22272585132720584298770693 4176109712385109556019505)
                ·
                  refine ⟨3132082284288832167014629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4176109712385109556019505 3132082284288832167014629)
                  ·
                    refine ⟨587265428304156031315243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3132082284288832167014629 587265428304156031315243)
                    ·
                      rfl

theorem cell23_3431086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3431086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431086 prefixEnd_3431086 := by exact prefixLift 3431086
  have htrace : WordTrace (prefixWord ++ tailWord_3431086) baseStart_3431086 baseEnd_3431086 := by
    simpa [prefixWord, tailWord_3431086, baseEnd_3431086] using wordTrace_append hprefix tailTrace_3431086
  have hstable : (prefixWord ++ tailWord_3431086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431086).length < 2 ^ (prefixWord ++ tailWord_3431086).sum := by decide
  have hdescent : baseEnd_3431086 < baseStart_3431086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431162 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_3431162 : Nat := 118140960795 + 3431162 * 2 ^ 59
def prefixEnd_3431162 : Nat := 4983230072969 + 3 ^ 40 * 3431162 * 2
def baseEnd_3431162 : Nat := 1761835309442209796595379

theorem tailTrace_3431162 : CollatzResearch.WordTrace tailWord_3431162 prefixEnd_3431162 1761835309442209796595379 := by
  unfold tailWord_3431162
  simp only [CollatzResearch.WordTrace]
  refine ⟨31286189798873386165299935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83429839463662363107466493 31286189798873386165299935)
  ·
    refine ⟨46929284698310079247949903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31286189798873386165299935 46929284698310079247949903)
    ·
      refine ⟨70393927047465118871924855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46929284698310079247949903 70393927047465118871924855)
      ·
        refine ⟨105590890571197678307887283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70393927047465118871924855 105590890571197678307887283)
        ·
          refine ⟨158386335856796517461830925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105590890571197678307887283 158386335856796517461830925)
          ·
            refine ⟨59394875946298694048186597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158386335856796517461830925 59394875946298694048186597)
            ·
              refine ⟨11136539239931005134034987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59394875946298694048186597 11136539239931005134034987)
              ·
                refine ⟨16704808859896507701052481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11136539239931005134034987 16704808859896507701052481)
                ·
                  refine ⟨12528606644922380775789361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16704808859896507701052481 12528606644922380775789361)
                  ·
                    refine ⟨9396454983691785581842021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12528606644922380775789361 9396454983691785581842021)
                    ·
                      refine ⟨1761835309442209796595379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9396454983691785581842021 1761835309442209796595379)
                      ·
                        rfl

theorem cell23_3431162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_3431162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431162 prefixEnd_3431162 := by exact prefixLift 3431162
  have htrace : WordTrace (prefixWord ++ tailWord_3431162) baseStart_3431162 baseEnd_3431162 := by
    simpa [prefixWord, tailWord_3431162, baseEnd_3431162] using wordTrace_append hprefix tailTrace_3431162
  have hstable : (prefixWord ++ tailWord_3431162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431162).length < 2 ^ (prefixWord ++ tailWord_3431162).sum := by decide
  have hdescent : baseEnd_3431162 < baseStart_3431162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431172 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 7]
def baseStart_3431172 : Nat := 118140960795 + 3431172 * 2 ^ 59
def prefixEnd_3431172 : Nat := 4983230072969 + 3 ^ 40 * 3431172 * 2
def baseEnd_3431172 : Nat := 195760049360972750830037

theorem tailTrace_3431172 : CollatzResearch.WordTrace tailWord_3431172 prefixEnd_3431172 195760049360972750830037 := by
  unfold tailWord_3431172
  simp only [CollatzResearch.WordTrace]
  refine ⟨62572561962728658184531885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83430082616971544246042513 62572561962728658184531885)
  ·
    refine ⟨23464710736023246819199457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62572561962728658184531885 23464710736023246819199457)
    ·
      refine ⟨17598533052017435114399593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23464710736023246819199457 17598533052017435114399593)
      ·
        refine ⟨13198899789013076335799695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17598533052017435114399593 13198899789013076335799695)
        ·
          refine ⟨19798349683519614503699543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13198899789013076335799695 19798349683519614503699543)
          ·
            refine ⟨29697524525279421755549315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19798349683519614503699543 29697524525279421755549315)
            ·
              refine ⟨44546286787919132633323973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29697524525279421755549315 44546286787919132633323973)
              ·
                refine ⟨8352428772734837368748245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44546286787919132633323973 8352428772734837368748245)
                ·
                  refine ⟨195760049360972750830037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8352428772734837368748245 195760049360972750830037)
                  ·
                    rfl

theorem cell23_3431172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_3431172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431172 prefixEnd_3431172 := by exact prefixLift 3431172
  have htrace : WordTrace (prefixWord ++ tailWord_3431172) baseStart_3431172 baseEnd_3431172 := by
    simpa [prefixWord, tailWord_3431172, baseEnd_3431172] using wordTrace_append hprefix tailTrace_3431172
  have hstable : (prefixWord ++ tailWord_3431172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431172).length < 2 ^ (prefixWord ++ tailWord_3431172).sum := by decide
  have hdescent : baseEnd_3431172 < baseStart_3431172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431186 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3431186 : Nat := 118140960795 + 3431186 * 2 ^ 59
def prefixEnd_3431186 : Nat := 4983230072969 + 3 ^ 40 * 3431186 * 2
def baseEnd_3431186 : Nat := 1761847632977917702695269

theorem tailTrace_3431186 : CollatzResearch.WordTrace tailWord_3431186 prefixEnd_3431186 1761847632977917702695269 := by
  unfold tailWord_3431186
  simp only [CollatzResearch.WordTrace]
  refine ⟨31286408636851649190018353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83430423031604397840048941 31286408636851649190018353)
  ·
    refine ⟨23464806477638736892513765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31286408636851649190018353 23464806477638736892513765)
    ·
      refine ⟨4399651214557263167346331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23464806477638736892513765 4399651214557263167346331)
      ·
        refine ⟨6599476821835894751019497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4399651214557263167346331 6599476821835894751019497)
        ·
          refine ⟨4949607616376921063264623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6599476821835894751019497 4949607616376921063264623)
          ·
            refine ⟨7424411424565381594896935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4949607616376921063264623 7424411424565381594896935)
            ·
              refine ⟨11136617136848072392345403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7424411424565381594896935 11136617136848072392345403)
              ·
                refine ⟨16704925705272108588518105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11136617136848072392345403 16704925705272108588518105)
                ·
                  refine ⟨12528694278954081441388579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16704925705272108588518105 12528694278954081441388579)
                  ·
                    refine ⟨18793041418431122162082869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12528694278954081441388579 18793041418431122162082869)
                    ·
                      refine ⟨1761847632977917702695269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18793041418431122162082869 1761847632977917702695269)
                      ·
                        rfl

theorem cell23_3431186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3431186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431186 prefixEnd_3431186 := by exact prefixLift 3431186
  have htrace : WordTrace (prefixWord ++ tailWord_3431186) baseStart_3431186 baseEnd_3431186 := by
    simpa [prefixWord, tailWord_3431186, baseEnd_3431186] using wordTrace_append hprefix tailTrace_3431186
  have hstable : (prefixWord ++ tailWord_3431186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431186).length < 2 ^ (prefixWord ++ tailWord_3431186).sum := by decide
  have hdescent : baseEnd_3431186 < baseStart_3431186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431212 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_3431212 : Nat := 118140960795 + 3431212 * 2 ^ 59
def prefixEnd_3431212 : Nat := 4983230072969 + 3 ^ 40 * 3431212 * 2
def baseEnd_3431212 : Nat := 1761860983474934600970149

theorem tailTrace_3431212 : CollatzResearch.WordTrace tailWord_3431212 prefixEnd_3431212 1761860983474934600970149 := by
  unfold tailWord_3431212
  simp only [CollatzResearch.WordTrace]
  refine ⟨62573291422656201600259945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83431055230208268800346593 62573291422656201600259945)
  ·
    refine ⟨46929968566992151200194959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62573291422656201600259945 46929968566992151200194959)
    ·
      refine ⟨70394952850488226800292439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46929968566992151200194959 70394952850488226800292439)
      ·
        refine ⟨105592429275732340200438659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70394952850488226800292439 105592429275732340200438659)
        ·
          refine ⟨158388643913598510300657989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105592429275732340200438659 158388643913598510300657989)
          ·
            refine ⟨29697870733799720681373373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158388643913598510300657989 29697870733799720681373373)
            ·
              refine ⟨11136701525174895255515015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29697870733799720681373373 11136701525174895255515015)
              ·
                refine ⟨16705052287762342883272523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11136701525174895255515015 16705052287762342883272523)
                ·
                  refine ⟨25057578431643514324908785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16705052287762342883272523 25057578431643514324908785)
                  ·
                    refine ⟨18793183823732635743681589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25057578431643514324908785 18793183823732635743681589)
                    ·
                      refine ⟨1761860983474934600970149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18793183823732635743681589 1761860983474934600970149)
                      ·
                        rfl

theorem cell23_3431212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_3431212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431212 prefixEnd_3431212 := by exact prefixLift 3431212
  have htrace : WordTrace (prefixWord ++ tailWord_3431212) baseStart_3431212 baseEnd_3431212 := by
    simpa [prefixWord, tailWord_3431212, baseEnd_3431212] using wordTrace_append hprefix tailTrace_3431212
  have hstable : (prefixWord ++ tailWord_3431212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431212).length < 2 ^ (prefixWord ++ tailWord_3431212).sum := by decide
  have hdescent : baseEnd_3431212 < baseStart_3431212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431239 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 4, 4, 2]
def baseStart_3431239 : Nat := 118140960795 + 3431239 * 2 ^ 59
def prefixEnd_3431239 : Nat := 4983230072969 + 3 ^ 40 * 3431239 * 2
def baseEnd_3431239 : Nat := 1761874847452605995332525

theorem tailTrace_3431239 : CollatzResearch.WordTrace tailWord_3431239 prefixEnd_3431239 1761874847452605995332525 := by
  unfold tailWord_3431239
  simp only [CollatzResearch.WordTrace]
  refine ⟨125147567616214586811752771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83431711744143057874501847 125147567616214586811752771)
  ·
    refine ⟨187721351424321880217629157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125147567616214586811752771 187721351424321880217629157)
    ·
      refine ⟨35197753392060352540805467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187721351424321880217629157 35197753392060352540805467)
      ·
        refine ⟨52796630088090528811208201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35197753392060352540805467 52796630088090528811208201)
        ·
          refine ⟨39597472566067896608406151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52796630088090528811208201 39597472566067896608406151)
          ·
            refine ⟨59396208849101844912609227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39597472566067896608406151 59396208849101844912609227)
            ·
              refine ⟨89094313273652767368913841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59396208849101844912609227 89094313273652767368913841)
              ·
                refine ⟨66820734955239575526685381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89094313273652767368913841 66820734955239575526685381)
                ·
                  refine ⟨12528887804107420411253509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66820734955239575526685381 12528887804107420411253509)
                  ·
                    refine ⟨2349166463270141327110033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12528887804107420411253509 2349166463270141327110033)
                    ·
                      refine ⟨1761874847452605995332525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349166463270141327110033 1761874847452605995332525)
                      ·
                        rfl

theorem cell23_3431239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_3431239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431239 prefixEnd_3431239 := by exact prefixLift 3431239
  have htrace : WordTrace (prefixWord ++ tailWord_3431239) baseStart_3431239 baseEnd_3431239 := by
    simpa [prefixWord, tailWord_3431239, baseEnd_3431239] using wordTrace_append hprefix tailTrace_3431239
  have hstable : (prefixWord ++ tailWord_3431239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431239).length < 2 ^ (prefixWord ++ tailWord_3431239).sum := by decide
  have hdescent : baseEnd_3431239 < baseStart_3431239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431312 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 4]
def baseStart_3431312 : Nat := 118140960795 + 3431312 * 2 ^ 59
def prefixEnd_3431312 : Nat := 4983230072969 + 3 ^ 40 * 3431312 * 2
def baseEnd_3431312 : Nat := 1761912331540384209719689

theorem tailTrace_3431312 : CollatzResearch.WordTrace tailWord_3431312 prefixEnd_3431312 1761912331540384209719689 := by
  unfold tailWord_3431312
  simp only [CollatzResearch.WordTrace]
  refine ⟨62575115072475060139580095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83433486763300080186106793 62575115072475060139580095)
  ·
    refine ⟨93862672608712590209370143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62575115072475060139580095 93862672608712590209370143)
    ·
      refine ⟨140794008913068885314055215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93862672608712590209370143 140794008913068885314055215)
      ·
        refine ⟨211191013369603327971082823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140794008913068885314055215 211191013369603327971082823)
        ·
          refine ⟨316786520054404991956624235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211191013369603327971082823 316786520054404991956624235)
          ·
            refine ⟨475179780081607487934936353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316786520054404991956624235 475179780081607487934936353)
            ·
              refine ⟨356384835061205615951202265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475179780081607487934936353 356384835061205615951202265)
              ·
                refine ⟨267288626295904211963401699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356384835061205615951202265 267288626295904211963401699)
                ·
                  refine ⟨400932939443856317945102549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267288626295904211963401699 400932939443856317945102549)
                  ·
                    refine ⟨9396865768215382451838341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 400932939443856317945102549 9396865768215382451838341)
                    ·
                      refine ⟨1761912331540384209719689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9396865768215382451838341 1761912331540384209719689)
                      ·
                        rfl

theorem cell23_3431312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_3431312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431312 prefixEnd_3431312 := by exact prefixLift 3431312
  have htrace : WordTrace (prefixWord ++ tailWord_3431312) baseStart_3431312 baseEnd_3431312 := by
    simpa [prefixWord, tailWord_3431312, baseEnd_3431312] using wordTrace_append hprefix tailTrace_3431312
  have hstable : (prefixWord ++ tailWord_3431312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431312).length < 2 ^ (prefixWord ++ tailWord_3431312).sum := by decide
  have hdescent : baseEnd_3431312 < baseStart_3431312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431349 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3431349 : Nat := 118140960795 + 3431349 * 2 ^ 59
def prefixEnd_3431349 : Nat := 4983230072969 + 3 ^ 40 * 3431349 * 2
def baseEnd_3431349 : Nat := 1761931330324600564957019

theorem tailTrace_3431349 : CollatzResearch.WordTrace tailWord_3431349 prefixEnd_3431349 1761931330324600564957019 := by
  unfold tailWord_3431349
  simp only [CollatzResearch.WordTrace]
  refine ⟨125151579645816075598257101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83434386430544050398838067 125151579645816075598257101)
  ·
    refine ⟨46931842367181028349346413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125151579645816075598257101 46931842367181028349346413)
    ·
      refine ⟨17599440887692885631004905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46931842367181028349346413 17599440887692885631004905)
      ·
        refine ⟨13199580665769664223253679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17599440887692885631004905 13199580665769664223253679)
        ·
          refine ⟨19799370998654496334880519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13199580665769664223253679 19799370998654496334880519)
          ·
            refine ⟨29699056497981744502320779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19799370998654496334880519 29699056497981744502320779)
            ·
              refine ⟨44548584746972616753481169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29699056497981744502320779 44548584746972616753481169)
              ·
                refine ⟨33411438560229462565110877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44548584746972616753481169 33411438560229462565110877)
                ·
                  refine ⟨12529289460086048461916579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33411438560229462565110877 12529289460086048461916579)
                  ·
                    refine ⟨18793934190129072692874869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12529289460086048461916579 18793934190129072692874869)
                    ·
                      refine ⟨1761931330324600564957019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18793934190129072692874869 1761931330324600564957019)
                      ·
                        rfl

theorem cell23_3431349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3431349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431349 prefixEnd_3431349 := by exact prefixLift 3431349
  have htrace : WordTrace (prefixWord ++ tailWord_3431349) baseStart_3431349 baseEnd_3431349 := by
    simpa [prefixWord, tailWord_3431349, baseEnd_3431349] using wordTrace_append hprefix tailTrace_3431349
  have hstable : (prefixWord ++ tailWord_3431349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431349).length < 2 ^ (prefixWord ++ tailWord_3431349).sum := by decide
  have hdescent : baseEnd_3431349 < baseStart_3431349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431357 : List Nat := [1, 4, 1, 2, 4, 2, 1, 3, 1, 1, 3]
def baseStart_3431357 : Nat := 118140960795 + 3431357 * 2 ^ 59
def prefixEnd_3431357 : Nat := 4983230072969 + 3 ^ 40 * 3431357 * 2
def baseEnd_3431357 : Nat := 1761935438169836533656983

theorem tailTrace_3431357 : CollatzResearch.WordTrace tailWord_3431357 prefixEnd_3431357 1761935438169836533656983 := by
  unfold tailWord_3431357
  simp only [CollatzResearch.WordTrace]
  refine ⟨125151871429787092964548325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83434580953191395309698883 125151871429787092964548325)
  ·
    refine ⟨23465975893085079930852811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125151871429787092964548325 23465975893085079930852811)
    ·
      refine ⟨35198963839627619896279217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23465975893085079930852811 35198963839627619896279217)
      ·
        refine ⟨26399222879720714922209413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35198963839627619896279217 26399222879720714922209413)
        ·
          refine ⟨4949854289947634047914265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26399222879720714922209413 4949854289947634047914265)
          ·
            refine ⟨3712390717460725535935699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4949854289947634047914265 3712390717460725535935699)
            ·
              refine ⟨5568586076191088303903549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712390717460725535935699 5568586076191088303903549)
              ·
                refine ⟨2088219778571658113963831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5568586076191088303903549 2088219778571658113963831)
                ·
                  refine ⟨3132329667857487170945747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088219778571658113963831 3132329667857487170945747)
                  ·
                    refine ⟨4698494501786230756418621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3132329667857487170945747 4698494501786230756418621)
                    ·
                      refine ⟨1761935438169836533656983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4698494501786230756418621 1761935438169836533656983)
                      ·
                        rfl

theorem cell23_3431357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_3431357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431357 prefixEnd_3431357 := by exact prefixLift 3431357
  have htrace : WordTrace (prefixWord ++ tailWord_3431357) baseStart_3431357 baseEnd_3431357 := by
    simpa [prefixWord, tailWord_3431357, baseEnd_3431357] using wordTrace_append hprefix tailTrace_3431357
  have hstable : (prefixWord ++ tailWord_3431357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431357).length < 2 ^ (prefixWord ++ tailWord_3431357).sum := by decide
  have hdescent : baseEnd_3431357 < baseStart_3431357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431380 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_3431380 : Nat := 118140960795 + 3431380 * 2 ^ 59
def prefixEnd_3431380 : Nat := 4983230072969 + 3 ^ 40 * 3431380 * 2
def baseEnd_3431380 : Nat := 1761947248224889943669377

theorem tailTrace_3431380 : CollatzResearch.WordTrace tailWord_3431380 prefixEnd_3431380 1761947248224889943669377 := by
  unfold tailWord_3431380
  simp only [CollatzResearch.WordTrace]
  refine ⟨62576355154351883946317797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83435140205802511928423729 62576355154351883946317797)
  ·
    refine ⟨11733066591440978239934587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62576355154351883946317797 11733066591440978239934587)
    ·
      refine ⟨17599599887161467359901881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11733066591440978239934587 17599599887161467359901881)
      ·
        refine ⟨13199699915371100519926411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17599599887161467359901881 13199699915371100519926411)
        ·
          refine ⟨19799549873056650779889617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13199699915371100519926411 19799549873056650779889617)
          ·
            refine ⟨14849662404792488084917213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19799549873056650779889617 14849662404792488084917213)
            ·
              refine ⟨5568623401797183031843955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14849662404792488084917213 5568623401797183031843955)
              ·
                refine ⟨8352935102695774547765933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568623401797183031843955 8352935102695774547765933)
                ·
                  refine ⟨3132350663510915455412225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8352935102695774547765933 3132350663510915455412225)
                  ·
                    refine ⟨2349262997633186591559169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3132350663510915455412225 2349262997633186591559169)
                    ·
                      refine ⟨1761947248224889943669377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349262997633186591559169 1761947248224889943669377)
                      ·
                        rfl

theorem cell23_3431380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_3431380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431380 prefixEnd_3431380 := by exact prefixLift 3431380
  have htrace : WordTrace (prefixWord ++ tailWord_3431380) baseStart_3431380 baseEnd_3431380 := by
    simpa [prefixWord, tailWord_3431380, baseEnd_3431380] using wordTrace_append hprefix tailTrace_3431380
  have hstable : (prefixWord ++ tailWord_3431380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431380).length < 2 ^ (prefixWord ++ tailWord_3431380).sum := by decide
  have hdescent : baseEnd_3431380 < baseStart_3431380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431396 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_3431396 : Nat := 118140960795 + 3431396 * 2 ^ 59
def prefixEnd_3431396 : Nat := 4983230072969 + 3 ^ 40 * 3431396 * 2
def baseEnd_3431396 : Nat := 1761955463915361881069303

theorem tailTrace_3431396 : CollatzResearch.WordTrace tailWord_3431396 prefixEnd_3431396 1761955463915361881069303 := by
  unfold tailWord_3431396
  simp only [CollatzResearch.WordTrace]
  refine ⟨62576646938322901312609021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83435529251097201750145361 62576646938322901312609021)
  ·
    refine ⟨23466242601871087992228383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62576646938322901312609021 23466242601871087992228383)
    ·
      refine ⟨35199363902806631988342575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23466242601871087992228383 35199363902806631988342575)
      ·
        refine ⟨52799045854209947982513863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35199363902806631988342575 52799045854209947982513863)
        ·
          refine ⟨79198568781314921973770795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52799045854209947982513863 79198568781314921973770795)
          ·
            refine ⟨118797853171972382960656193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79198568781314921973770795 118797853171972382960656193)
            ·
              refine ⟨89098389878979287220492145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118797853171972382960656193 89098389878979287220492145)
              ·
                refine ⟨66823792409234465415369109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89098389878979287220492145 66823792409234465415369109)
                ·
                  refine ⟨3132365269182865566345427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66823792409234465415369109 3132365269182865566345427)
                  ·
                    refine ⟨4698547903774298349518141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3132365269182865566345427 4698547903774298349518141)
                    ·
                      refine ⟨1761955463915361881069303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4698547903774298349518141 1761955463915361881069303)
                      ·
                        rfl

theorem cell23_3431396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_3431396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431396 prefixEnd_3431396 := by exact prefixLift 3431396
  have htrace : WordTrace (prefixWord ++ tailWord_3431396) baseStart_3431396 baseEnd_3431396 := by
    simpa [prefixWord, tailWord_3431396, baseEnd_3431396] using wordTrace_append hprefix tailTrace_3431396
  have hstable : (prefixWord ++ tailWord_3431396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431396).length < 2 ^ (prefixWord ++ tailWord_3431396).sum := by decide
  have hdescent : baseEnd_3431396 < baseStart_3431396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431397 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 1, 1, 4]
def baseStart_3431397 : Nat := 118140960795 + 3431397 * 2 ^ 59
def prefixEnd_3431397 : Nat := 4983230072969 + 3 ^ 40 * 3431397 * 2
def baseEnd_3431397 : Nat := 1761955977396016377156799

theorem tailTrace_3431397 : CollatzResearch.WordTrace tailWord_3431397 prefixEnd_3431397 1761955977396016377156799 := by
  unfold tailWord_3431397
  simp only [CollatzResearch.WordTrace]
  refine ⟨125153330349642179796004445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83435553566428119864002963 125153330349642179796004445)
  ·
    refine ⟨46932498881115817423501667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125153330349642179796004445 46932498881115817423501667)
    ·
      refine ⟨70398748321673726135252501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46932498881115817423501667 70398748321673726135252501)
      ·
        refine ⟨3299941327578455912589961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70398748321673726135252501 3299941327578455912589961)
        ·
          refine ⟨2474955995683841934442471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3299941327578455912589961 2474955995683841934442471)
          ·
            refine ⟨3712433993525762901663707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474955995683841934442471 3712433993525762901663707)
            ·
              refine ⟨5568650990288644352495561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712433993525762901663707 5568650990288644352495561)
              ·
                refine ⟨4176488242716483264371671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5568650990288644352495561 4176488242716483264371671)
                ·
                  refine ⟨6264732364074724896557507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176488242716483264371671 6264732364074724896557507)
                  ·
                    refine ⟨9397098546112087344836261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6264732364074724896557507 9397098546112087344836261)
                    ·
                      refine ⟨1761955977396016377156799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9397098546112087344836261 1761955977396016377156799)
                      ·
                        rfl

theorem cell23_3431397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_3431397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431397 prefixEnd_3431397 := by exact prefixLift 3431397
  have htrace : WordTrace (prefixWord ++ tailWord_3431397) baseStart_3431397 baseEnd_3431397 := by
    simpa [prefixWord, tailWord_3431397, baseEnd_3431397] using wordTrace_append hprefix tailTrace_3431397
  have hstable : (prefixWord ++ tailWord_3431397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431397).length < 2 ^ (prefixWord ++ tailWord_3431397).sum := by decide
  have hdescent : baseEnd_3431397 < baseStart_3431397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431429 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_3431429 : Nat := 118140960795 + 3431429 * 2 ^ 59
def prefixEnd_3431429 : Nat := 4983230072969 + 3 ^ 40 * 3431429 * 2
def baseEnd_3431429 : Nat := 587324136258986750652217

theorem tailTrace_3431429 : CollatzResearch.WordTrace tailWord_3431429 prefixEnd_3431429 587324136258986750652217 := by
  unfold tailWord_3431429
  simp only [CollatzResearch.WordTrace]
  refine ⟨125154497485526249261169341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83436331657017499507446227 125154497485526249261169341)
  ·
    refine ⟨46932936557072343472938503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125154497485526249261169341 46932936557072343472938503)
    ·
      refine ⟨70399404835608515209407755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46932936557072343472938503 70399404835608515209407755)
      ·
        refine ⟨105599107253412772814111633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70399404835608515209407755 105599107253412772814111633)
        ·
          refine ⟨79199330440059579610583725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105599107253412772814111633 79199330440059579610583725)
          ·
            refine ⟨29699748915022342353968897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79199330440059579610583725 29699748915022342353968897)
            ·
              refine ⟨22274811686266756765476673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29699748915022342353968897 22274811686266756765476673)
              ·
                refine ⟨16706108764700067574107505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22274811686266756765476673 16706108764700067574107505)
                ·
                  refine ⟨12529581573525050680580629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16706108764700067574107505 12529581573525050680580629)
                  ·
                    refine ⟨587324136258986750652217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12529581573525050680580629 587324136258986750652217)
                    ·
                      rfl

theorem cell23_3431429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_3431429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431429 prefixEnd_3431429 := by exact prefixLift 3431429
  have htrace : WordTrace (prefixWord ++ tailWord_3431429) baseStart_3431429 baseEnd_3431429 := by
    simpa [prefixWord, tailWord_3431429, baseEnd_3431429] using wordTrace_append hprefix tailTrace_3431429
  have hstable : (prefixWord ++ tailWord_3431429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431429).length < 2 ^ (prefixWord ++ tailWord_3431429).sum := by decide
  have hdescent : baseEnd_3431429 < baseStart_3431429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431449 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 4]
def baseStart_3431449 : Nat := 118140960795 + 3431449 * 2 ^ 59
def prefixEnd_3431449 : Nat := 4983230072969 + 3 ^ 40 * 3431449 * 2
def baseEnd_3431449 : Nat := 1761982678390050173706559

theorem tailTrace_3431449 : CollatzResearch.WordTrace tailWord_3431449 prefixEnd_3431449 1761982678390050173706559 := by
  unfold tailWord_3431449
  simp only [CollatzResearch.WordTrace]
  refine ⟨125155226945453792676897401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83436817963635861784598267 125155226945453792676897401)
  ·
    refine ⟨93866420209090344507673051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125155226945453792676897401 93866420209090344507673051)
    ·
      refine ⟨140799630313635516761509577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93866420209090344507673051 140799630313635516761509577)
      ·
        refine ⟨105599722735226637571132183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140799630313635516761509577 105599722735226637571132183)
        ·
          refine ⟨158399584102839956356698275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105599722735226637571132183 158399584102839956356698275)
          ·
            refine ⟨237599376154259934535047413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158399584102839956356698275 237599376154259934535047413)
            ·
              refine ⟨22274941514461868862660695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237599376154259934535047413 22274941514461868862660695)
              ·
                refine ⟨33412412271692803293991043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22274941514461868862660695 33412412271692803293991043)
                ·
                  refine ⟨50118618407539204940986565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33412412271692803293991043 50118618407539204940986565)
                  ·
                    refine ⟨9397240951413600926434981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50118618407539204940986565 9397240951413600926434981)
                    ·
                      refine ⟨1761982678390050173706559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9397240951413600926434981 1761982678390050173706559)
                      ·
                        rfl

theorem cell23_3431449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_3431449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431449 prefixEnd_3431449 := by exact prefixLift 3431449
  have htrace : WordTrace (prefixWord ++ tailWord_3431449) baseStart_3431449 baseEnd_3431449 := by
    simpa [prefixWord, tailWord_3431449, baseEnd_3431449] using wordTrace_append hprefix tailTrace_3431449
  have hstable : (prefixWord ++ tailWord_3431449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431449).length < 2 ^ (prefixWord ++ tailWord_3431449).sum := by decide
  have hdescent : baseEnd_3431449 < baseStart_3431449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431459 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 9]
def baseStart_3431459 : Nat := 118140960795 + 3431459 * 2 ^ 59
def prefixEnd_3431459 : Nat := 4983230072969 + 3 ^ 40 * 3431459 * 2
def baseEnd_3431459 : Nat := 195776423688510570509057

theorem tailTrace_3431459 : CollatzResearch.WordTrace tailWord_3431459 prefixEnd_3431459 195776423688510570509057 := by
  unfold tailWord_3431459
  simp only [CollatzResearch.WordTrace]
  refine ⟨125155591675417564384761431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83437061116945042923174287 125155591675417564384761431)
  ·
    refine ⟨187733387513126346577142147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125155591675417564384761431 187733387513126346577142147)
    ·
      refine ⟨281600081269689519865713221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187733387513126346577142147 281600081269689519865713221)
      ·
        refine ⟨52800015238066784974821229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281600081269689519865713221 52800015238066784974821229)
        ·
          refine ⟨19800005714275044365557961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52800015238066784974821229 19800005714275044365557961)
          ·
            refine ⟨14850004285706283274168471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19800005714275044365557961 14850004285706283274168471)
            ·
              refine ⟨22275006428559424911252707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14850004285706283274168471 22275006428559424911252707)
              ·
                refine ⟨33412509642839137366879061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22275006428559424911252707 33412509642839137366879061)
                ·
                  refine ⟨195776423688510570509057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33412509642839137366879061 195776423688510570509057)
                  ·
                    rfl

theorem cell23_3431459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 9].length) (baseStart_3431459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431459 prefixEnd_3431459 := by exact prefixLift 3431459
  have htrace : WordTrace (prefixWord ++ tailWord_3431459) baseStart_3431459 baseEnd_3431459 := by
    simpa [prefixWord, tailWord_3431459, baseEnd_3431459] using wordTrace_append hprefix tailTrace_3431459
  have hstable : (prefixWord ++ tailWord_3431459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431459).length < 2 ^ (prefixWord ++ tailWord_3431459).sum := by decide
  have hdescent : baseEnd_3431459 < baseStart_3431459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431470 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_3431470 : Nat := 118140960795 + 3431470 * 2 ^ 59
def prefixEnd_3431470 : Nat := 4983230072969 + 3 ^ 40 * 3431470 * 2
def baseEnd_3431470 : Nat := 1761993461483794591543963

theorem tailTrace_3431470 : CollatzResearch.WordTrace tailWord_3431470 prefixEnd_3431470 1761993461483794591543963 := by
  unfold tailWord_3431470
  simp only [CollatzResearch.WordTrace]
  refine ⟨15644499109797214157926483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83437328585585142175607909 15644499109797214157926483)
  ·
    refine ⟨23466748664695821236889725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15644499109797214157926483 23466748664695821236889725)
    ·
      refine ⟨8800030749260932963833647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23466748664695821236889725 8800030749260932963833647)
      ·
        refine ⟨13200046123891399445750471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8800030749260932963833647 13200046123891399445750471)
        ·
          refine ⟨19800069185837099168625707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13200046123891399445750471 19800069185837099168625707)
          ·
            refine ⟨29700103778755648752938561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19800069185837099168625707 29700103778755648752938561)
            ·
              refine ⟨22275077834066736564703921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29700103778755648752938561 22275077834066736564703921)
              ·
                refine ⟨16706308375550052423527941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22275077834066736564703921 16706308375550052423527941)
                ·
                  refine ⟨3132432820415634829411489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16706308375550052423527941 3132432820415634829411489)
                  ·
                    refine ⟨2349324615311726122058617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3132432820415634829411489 2349324615311726122058617)
                    ·
                      refine ⟨1761993461483794591543963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349324615311726122058617 1761993461483794591543963)
                      ·
                        rfl

theorem cell23_3431470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_3431470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431470 prefixEnd_3431470 := by exact prefixLift 3431470
  have htrace : WordTrace (prefixWord ++ tailWord_3431470) baseStart_3431470 baseEnd_3431470 := by
    simpa [prefixWord, tailWord_3431470, baseEnd_3431470] using wordTrace_append hprefix tailTrace_3431470
  have hstable : (prefixWord ++ tailWord_3431470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431470).length < 2 ^ (prefixWord ++ tailWord_3431470).sum := by decide
  have hdescent : baseEnd_3431470 < baseStart_3431470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431506 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_3431506 : Nat := 118140960795 + 3431506 * 2 ^ 59
def prefixEnd_3431506 : Nat := 4983230072969 + 3 ^ 40 * 3431506 * 2
def baseEnd_3431506 : Nat := 587337315595785483564599

theorem tailTrace_3431506 : CollatzResearch.WordTrace tailWord_3431506 prefixEnd_3431506 587337315595785483564599 := by
  unfold tailWord_3431506
  simp only [CollatzResearch.WordTrace]
  refine ⟨31289326476561822852930593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83438203937498194274481581 31289326476561822852930593)
  ·
    refine ⟨23466994857421367139697945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31289326476561822852930593 23466994857421367139697945)
    ·
      refine ⟨17600246143066025354773459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23466994857421367139697945 17600246143066025354773459)
      ·
        refine ⟨26400369214599038032160189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17600246143066025354773459 26400369214599038032160189)
        ·
          refine ⟨9900138455474639262060071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26400369214599038032160189 9900138455474639262060071)
          ·
            refine ⟨14850207683211958893090107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9900138455474639262060071 14850207683211958893090107)
            ·
              refine ⟨22275311524817938339635161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14850207683211958893090107 22275311524817938339635161)
              ·
                refine ⟨16706483643613453754726371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22275311524817938339635161 16706483643613453754726371)
                ·
                  refine ⟨25059725465420180632089557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16706483643613453754726371 25059725465420180632089557)
                  ·
                    refine ⟨587337315595785483564599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25059725465420180632089557 587337315595785483564599)
                    ·
                      rfl

theorem cell23_3431506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_3431506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431506 prefixEnd_3431506 := by exact prefixLift 3431506
  have htrace : WordTrace (prefixWord ++ tailWord_3431506) baseStart_3431506 baseEnd_3431506 := by
    simpa [prefixWord, tailWord_3431506, baseEnd_3431506] using wordTrace_append hprefix tailTrace_3431506
  have hstable : (prefixWord ++ tailWord_3431506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431506).length < 2 ^ (prefixWord ++ tailWord_3431506).sum := by decide
  have hdescent : baseEnd_3431506 < baseStart_3431506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431519 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 2, 8]
def baseStart_3431519 : Nat := 118140960795 + 3431519 * 2 ^ 59
def prefixEnd_3431519 : Nat := 4983230072969 + 3 ^ 40 * 3431519 * 2
def baseEnd_3431519 : Nat := 587339540678621633277079

theorem tailTrace_3431519 : CollatzResearch.WordTrace tailWord_3431519 prefixEnd_3431519 587339540678621633277079 := by
  unfold tailWord_3431519
  simp only [CollatzResearch.WordTrace]
  refine ⟨125157780055200194631945611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83438520036800129754630407 125157780055200194631945611)
  ·
    refine ⟨187736670082800291947918417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125157780055200194631945611 187736670082800291947918417)
    ·
      refine ⟨140802502562100218960938813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187736670082800291947918417 140802502562100218960938813)
      ·
        refine ⟨52800938460787582110352055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140802502562100218960938813 52800938460787582110352055)
        ·
          refine ⟨79201407691181373165528083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52800938460787582110352055 79201407691181373165528083)
          ·
            refine ⟨118802111536772059748292125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79201407691181373165528083 118802111536772059748292125)
            ·
              refine ⟨44550791826289522405609547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118802111536772059748292125 44550791826289522405609547)
              ·
                refine ⟨66826187739434283608414321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44550791826289522405609547 66826187739434283608414321)
                ·
                  refine ⟨50119640804575712706310741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66826187739434283608414321 50119640804575712706310741)
                  ·
                    refine ⟨587339540678621633277079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50119640804575712706310741 587339540678621633277079)
                    ·
                      rfl

theorem cell23_3431519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_3431519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431519 prefixEnd_3431519 := by exact prefixLift 3431519
  have htrace : WordTrace (prefixWord ++ tailWord_3431519) baseStart_3431519 baseEnd_3431519 := by
    simpa [prefixWord, tailWord_3431519, baseEnd_3431519] using wordTrace_append hprefix tailTrace_3431519
  have hstable : (prefixWord ++ tailWord_3431519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431519).length < 2 ^ (prefixWord ++ tailWord_3431519).sum := by decide
  have hdescent : baseEnd_3431519 < baseStart_3431519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431580 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3431580 : Nat := 118140960795 + 3431580 * 2 ^ 59
def prefixEnd_3431580 : Nat := 4983230072969 + 3 ^ 40 * 3431580 * 2
def baseEnd_3431580 : Nat := 1762049944355789161168457

theorem tailTrace_3431580 : CollatzResearch.WordTrace tailWord_3431580 prefixEnd_3431580 1762049944355789161168457 := by
  unfold tailWord_3431580
  simp only [CollatzResearch.WordTrace]
  refine ⟨62580002453989601024958097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83440003271986134699944129 62580002453989601024958097)
  ·
    refine ⟨46935001840492200768718573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62580002453989601024958097 46935001840492200768718573)
    ·
      refine ⟨17600625690184575288269465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46935001840492200768718573 17600625690184575288269465)
      ·
        refine ⟨13200469267638431466202099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17600625690184575288269465 13200469267638431466202099)
        ·
          refine ⟨19800703901457647199303149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13200469267638431466202099 19800703901457647199303149)
          ·
            refine ⟨7425263963046617699738681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19800703901457647199303149 7425263963046617699738681)
            ·
              refine ⟨5568947972284963274804011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425263963046617699738681 5568947972284963274804011)
              ·
                refine ⟨8353421958427444912206017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568947972284963274804011 8353421958427444912206017)
                ·
                  refine ⟨6265066468820583684154513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8353421958427444912206017 6265066468820583684154513)
                  ·
                    refine ⟨4698799851615437763115885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6265066468820583684154513 4698799851615437763115885)
                    ·
                      refine ⟨1762049944355789161168457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4698799851615437763115885 1762049944355789161168457)
                      ·
                        rfl

theorem cell23_3431580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3431580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431580 prefixEnd_3431580 := by exact prefixLift 3431580
  have htrace : WordTrace (prefixWord ++ tailWord_3431580) baseStart_3431580 baseEnd_3431580 := by
    simpa [prefixWord, tailWord_3431580, baseEnd_3431580] using wordTrace_append hprefix tailTrace_3431580
  have hstable : (prefixWord ++ tailWord_3431580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431580).length < 2 ^ (prefixWord ++ tailWord_3431580).sum := by decide
  have hdescent : baseEnd_3431580 < baseStart_3431580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431633 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 4]
def baseStart_3431633 : Nat := 118140960795 + 3431633 * 2 ^ 59
def prefixEnd_3431633 : Nat := 4983230072969 + 3 ^ 40 * 3431633 * 2
def baseEnd_3431633 : Nat := 1762077158830477453805713

theorem tailTrace_3431633 : CollatzResearch.WordTrace tailWord_3431633 prefixEnd_3431633 1762077158830477453805713 := by
  unfold tailWord_3431633
  simp only [CollatzResearch.WordTrace]
  refine ⟨125161937976787192101595553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83441291984524794734397035 125161937976787192101595553)
  ·
    refine ⟨93871453482590394076196665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125161937976787192101595553 93871453482590394076196665)
    ·
      refine ⟨70403590111942795557147499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93871453482590394076196665 70403590111942795557147499)
      ·
        refine ⟨105605385167914193335721249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70403590111942795557147499 105605385167914193335721249)
        ·
          refine ⟨79204038875935645001790937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105605385167914193335721249 79204038875935645001790937)
          ·
            refine ⟨59403029156951733751343203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79204038875935645001790937 59403029156951733751343203)
            ·
              refine ⟨89104543735427600627014805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59403029156951733751343203 89104543735427600627014805)
              ·
                refine ⟨4176775487598168779391319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89104543735427600627014805 4176775487598168779391319)
                ·
                  refine ⟨6265163231397253169086979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176775487598168779391319 6265163231397253169086979)
                  ·
                    refine ⟨9397744847095879753630469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6265163231397253169086979 9397744847095879753630469)
                    ·
                      refine ⟨1762077158830477453805713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9397744847095879753630469 1762077158830477453805713)
                      ·
                        rfl

theorem cell23_3431633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_3431633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431633 prefixEnd_3431633 := by exact prefixLift 3431633
  have htrace : WordTrace (prefixWord ++ tailWord_3431633) baseStart_3431633 baseEnd_3431633 := by
    simpa [prefixWord, tailWord_3431633, baseEnd_3431633] using wordTrace_append hprefix tailTrace_3431633
  have hstable : (prefixWord ++ tailWord_3431633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431633).length < 2 ^ (prefixWord ++ tailWord_3431633).sum := by decide
  have hdescent : baseEnd_3431633 < baseStart_3431633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431637 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 2, 3, 2]
def baseStart_3431637 : Nat := 118140960795 + 3431637 * 2 ^ 59
def prefixEnd_3431637 : Nat := 4983230072969 + 3 ^ 40 * 3431637 * 2
def baseEnd_3431637 : Nat := 1762079212753095438155695

theorem tailTrace_3431637 : CollatzResearch.WordTrace tailWord_3431637 prefixEnd_3431637 1762079212753095438155695 := by
  unfold tailWord_3431637
  simp only [CollatzResearch.WordTrace]
  refine ⟨125162083868772700784741165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83441389245848467189827443 125162083868772700784741165)
  ·
    refine ⟨46935781450789762794277937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125162083868772700784741165 46935781450789762794277937)
    ·
      refine ⟨35201836088092322095708453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46935781450789762794277937 35201836088092322095708453)
      ·
        refine ⟨6600344266517310392945335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35201836088092322095708453 6600344266517310392945335)
        ·
          refine ⟨9900516399775965589418003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6600344266517310392945335 9900516399775965589418003)
          ·
            refine ⟨14850774599663948384127005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9900516399775965589418003 14850774599663948384127005)
            ·
              refine ⟨5569040474873980644047627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14850774599663948384127005 5569040474873980644047627)
              ·
                refine ⟨8353560712310970966071441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5569040474873980644047627 8353560712310970966071441)
                ·
                  refine ⟨6265170534233228224553581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8353560712310970966071441 6265170534233228224553581)
                  ·
                    refine ⟨2349438950337460584207593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6265170534233228224553581 2349438950337460584207593)
                    ·
                      refine ⟨1762079212753095438155695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349438950337460584207593 1762079212753095438155695)
                      ·
                        rfl

theorem cell23_3431637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_3431637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431637 prefixEnd_3431637 := by exact prefixLift 3431637
  have htrace : WordTrace (prefixWord ++ tailWord_3431637) baseStart_3431637 baseEnd_3431637 := by
    simpa [prefixWord, tailWord_3431637, baseEnd_3431637] using wordTrace_append hprefix tailTrace_3431637
  have hstable : (prefixWord ++ tailWord_3431637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431637).length < 2 ^ (prefixWord ++ tailWord_3431637).sum := by decide
  have hdescent : baseEnd_3431637 < baseStart_3431637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431656 : List Nat := [2, 1, 4, 1, 2, 1, 12]
def baseStart_3431656 : Nat := 118140960795 + 3431656 * 2 ^ 59
def prefixEnd_3431656 : Nat := 4983230072969 + 3 ^ 40 * 3431656 * 2
def baseEnd_3431656 : Nat := 21754184801055936590347

theorem tailTrace_3431656 : CollatzResearch.WordTrace tailWord_3431656 prefixEnd_3431656 21754184801055936590347 := by
  unfold tailWord_3431656
  simp only [CollatzResearch.WordTrace]
  refine ⟨62581388427851933514841411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83441851237135911353121881 62581388427851933514841411)
  ·
    refine ⟨93872082641777900272262117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62581388427851933514841411 93872082641777900272262117)
    ·
      refine ⟨17601015495333356301049147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93872082641777900272262117 17601015495333356301049147)
      ·
        refine ⟨26401523243000034451573721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17601015495333356301049147 26401523243000034451573721)
        ·
          refine ⟨19801142432250025838680291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26401523243000034451573721 19801142432250025838680291)
          ·
            refine ⟨29701713648375038758020437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19801142432250025838680291 29701713648375038758020437)
            ·
              refine ⟨21754184801055936590347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 29701713648375038758020437 21754184801055936590347)
              ·
                rfl

theorem cell23_3431656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 12].length) (baseStart_3431656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431656 prefixEnd_3431656 := by exact prefixLift 3431656
  have htrace : WordTrace (prefixWord ++ tailWord_3431656) baseStart_3431656 baseEnd_3431656 := by
    simpa [prefixWord, tailWord_3431656, baseEnd_3431656] using wordTrace_append hprefix tailTrace_3431656
  have hstable : (prefixWord ++ tailWord_3431656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431656).length < 2 ^ (prefixWord ++ tailWord_3431656).sum := by decide
  have hdescent : baseEnd_3431656 < baseStart_3431656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431660 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 2, 4]
def baseStart_3431660 : Nat := 118140960795 + 3431660 * 2 ^ 59
def prefixEnd_3431660 : Nat := 4983230072969 + 3 ^ 40 * 3431660 * 2
def baseEnd_3431660 : Nat := 587363674269382949389363

theorem tailTrace_3431660 : CollatzResearch.WordTrace tailWord_3431660 prefixEnd_3431660 587363674269382949389363 := by
  unfold tailWord_3431660
  simp only [CollatzResearch.WordTrace]
  refine ⟨62581461373844687856414217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83441948498459583808552289 62581461373844687856414217)
  ·
    refine ⟨46936096030383515892310663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62581461373844687856414217 46936096030383515892310663)
    ·
      refine ⟨70404144045575273838465995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46936096030383515892310663 70404144045575273838465995)
      ·
        refine ⟨105606216068362910757698993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70404144045575273838465995 105606216068362910757698993)
        ·
          refine ⟨79204662051272183068274245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105606216068362910757698993 79204662051272183068274245)
          ·
            refine ⟨14850874134613534325301421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79204662051272183068274245 14850874134613534325301421)
            ·
              refine ⟨5569077800480075371988033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14850874134613534325301421 5569077800480075371988033)
              ·
                refine ⟨4176808350360056528991025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5569077800480075371988033 4176808350360056528991025)
                ·
                  refine ⟨3132606262770042396743269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4176808350360056528991025 3132606262770042396743269)
                  ·
                    refine ⟨587363674269382949389363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3132606262770042396743269 587363674269382949389363)
                    ·
                      rfl

theorem cell23_3431660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_3431660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431660 prefixEnd_3431660 := by exact prefixLift 3431660
  have htrace : WordTrace (prefixWord ++ tailWord_3431660) baseStart_3431660 baseEnd_3431660 := by
    simpa [prefixWord, tailWord_3431660, baseEnd_3431660] using wordTrace_append hprefix tailTrace_3431660
  have hstable : (prefixWord ++ tailWord_3431660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431660).length < 2 ^ (prefixWord ++ tailWord_3431660).sum := by decide
  have hdescent : baseEnd_3431660 < baseStart_3431660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431667 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 3, 2, 2]
def baseStart_3431667 : Nat := 118140960795 + 3431667 * 2 ^ 59
def prefixEnd_3431667 : Nat := 4983230072969 + 3 ^ 40 * 3431667 * 2
def baseEnd_3431667 : Nat := 1762094617172730320780557

theorem tailTrace_3431667 : CollatzResearch.WordTrace tailWord_3431667 prefixEnd_3431667 1762094617172730320780557 := by
  unfold tailWord_3431667
  simp only [CollatzResearch.WordTrace]
  refine ⟨125163178058664015908333255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83442118705776010605555503 125163178058664015908333255)
  ·
    refine ⟨187744767087996023862499883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125163178058664015908333255 187744767087996023862499883)
    ·
      refine ⟨281617150631994035793749825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187744767087996023862499883 281617150631994035793749825)
      ·
        refine ⟨211212862973995526845312369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281617150631994035793749825 211212862973995526845312369)
        ·
          refine ⟨158409647230496645133984277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211212862973995526845312369 158409647230496645133984277)
          ·
            refine ⟨7425452213929530240655513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158409647230496645133984277 7425452213929530240655513)
            ·
              refine ⟨5569089160447147680491635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425452213929530240655513 5569089160447147680491635)
              ·
                refine ⟨8353633740670721520737453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5569089160447147680491635 8353633740670721520737453)
                ·
                  refine ⟨3132612652751520570276545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8353633740670721520737453 3132612652751520570276545)
                  ·
                    refine ⟨2349459489563640427707409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3132612652751520570276545 2349459489563640427707409)
                    ·
                      refine ⟨1762094617172730320780557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349459489563640427707409 1762094617172730320780557)
                      ·
                        rfl

theorem cell23_3431667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 2, 2].length) (baseStart_3431667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431667 prefixEnd_3431667 := by exact prefixLift 3431667
  have htrace : WordTrace (prefixWord ++ tailWord_3431667) baseStart_3431667 baseEnd_3431667 := by
    simpa [prefixWord, tailWord_3431667, baseEnd_3431667] using wordTrace_append hprefix tailTrace_3431667
  have hstable : (prefixWord ++ tailWord_3431667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431667).length < 2 ^ (prefixWord ++ tailWord_3431667).sum := by decide
  have hdescent : baseEnd_3431667 < baseStart_3431667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431743 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 5]
def baseStart_3431743 : Nat := 118140960795 + 3431743 * 2 ^ 59
def prefixEnd_3431743 : Nat := 4983230072969 + 3 ^ 40 * 3431743 * 2
def baseEnd_3431743 : Nat := 1762133641702472023430207

theorem tailTrace_3431743 : CollatzResearch.WordTrace tailWord_3431743 prefixEnd_3431743 1762133641702472023430207 := by
  unfold tailWord_3431743
  simp only [CollatzResearch.WordTrace]
  refine ⟨125165950006388680888099883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83443966670925787258733255 125165950006388680888099883)
  ·
    refine ⟨187748925009583021332149825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125165950006388680888099883 187748925009583021332149825)
    ·
      refine ⟨140811693757187265999112369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187748925009583021332149825 140811693757187265999112369)
      ·
        refine ⟨105608770317890449499334277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140811693757187265999112369 105608770317890449499334277)
        ·
          refine ⟨19801644434604459281125177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105608770317890449499334277 19801644434604459281125177)
          ·
            refine ⟨14851233325953344460843883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19801644434604459281125177 14851233325953344460843883)
            ·
              refine ⟨22276849988930016691265825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14851233325953344460843883 22276849988930016691265825)
              ·
                refine ⟨16707637491697512518449369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22276849988930016691265825 16707637491697512518449369)
                ·
                  refine ⟨12530728118773134388837027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16707637491697512518449369 12530728118773134388837027)
                  ·
                    refine ⟨18796092178159701583255541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12530728118773134388837027 18796092178159701583255541)
                    ·
                      refine ⟨1762133641702472023430207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18796092178159701583255541 1762133641702472023430207)
                      ·
                        rfl

theorem cell23_3431743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_3431743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431743 prefixEnd_3431743 := by exact prefixLift 3431743
  have htrace : WordTrace (prefixWord ++ tailWord_3431743) baseStart_3431743 baseEnd_3431743 := by
    simpa [prefixWord, tailWord_3431743, baseEnd_3431743] using wordTrace_append hprefix tailTrace_3431743
  have hstable : (prefixWord ++ tailWord_3431743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431743).length < 2 ^ (prefixWord ++ tailWord_3431743).sum := by decide
  have hdescent : baseEnd_3431743 < baseStart_3431743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431793 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 4, 5]
def baseStart_3431793 : Nat := 118140960795 + 3431793 * 2 ^ 59
def prefixEnd_3431793 : Nat := 4983230072969 + 3 ^ 40 * 3431793 * 2
def baseEnd_3431793 : Nat := 587386438578398942601659

theorem tailTrace_3431793 : CollatzResearch.WordTrace tailWord_3431793 prefixEnd_3431793 587386438578398942601659 := by
  unfold tailWord_3431793
  simp only [CollatzResearch.WordTrace]
  refine ⟨125167773656207539427420033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83445182437471692951613355 125167773656207539427420033)
  ·
    refine ⟨93875830242155654570565025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125167773656207539427420033 93875830242155654570565025)
    ·
      refine ⟨70406872681616740927923769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93875830242155654570565025 70406872681616740927923769)
      ·
        refine ⟨52805154511212555695942827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70406872681616740927923769 52805154511212555695942827)
        ·
          refine ⟨79207731766818833543914241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52805154511212555695942827 79207731766818833543914241)
          ·
            refine ⟨59405798825114125157935681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79207731766818833543914241 59405798825114125157935681)
            ·
              refine ⟨44554349118835593868451761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59405798825114125157935681 44554349118835593868451761)
              ·
                refine ⟨33415761839126695401338821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44554349118835593868451761 33415761839126695401338821)
                ·
                  refine ⟨6265455344836255387751029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33415761839126695401338821 6265455344836255387751029)
                  ·
                    refine ⟨587386438578398942601659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6265455344836255387751029 587386438578398942601659)
                    ·
                      rfl

theorem cell23_3431793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_3431793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431793 prefixEnd_3431793 := by exact prefixLift 3431793
  have htrace : WordTrace (prefixWord ++ tailWord_3431793) baseStart_3431793 baseEnd_3431793 := by
    simpa [prefixWord, tailWord_3431793, baseEnd_3431793] using wordTrace_append hprefix tailTrace_3431793
  have hstable : (prefixWord ++ tailWord_3431793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431793).length < 2 ^ (prefixWord ++ tailWord_3431793).sum := by decide
  have hdescent : baseEnd_3431793 < baseStart_3431793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431843 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 6]
def baseStart_3431843 : Nat := 118140960795 + 3431843 * 2 ^ 59
def prefixEnd_3431843 : Nat := 4983230072969 + 3 ^ 40 * 3431843 * 2
def baseEnd_3431843 : Nat := 1762184989767921632179747

theorem tailTrace_3431843 : CollatzResearch.WordTrace tailWord_3431843 prefixEnd_3431843 1762184989767921632179747 := by
  unfold tailWord_3431843
  simp only [CollatzResearch.WordTrace]
  refine ⟨125169597306026397966740183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83446398204017598644493455 125169597306026397966740183)
  ·
    refine ⟨187754395959039596950110275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125169597306026397966740183 187754395959039596950110275)
    ·
      refine ⟨281631593938559395425165413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187754395959039596950110275 281631593938559395425165413)
      ·
        refine ⟨52805923863479886642218515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281631593938559395425165413 52805923863479886642218515)
        ·
          refine ⟨79208885795219829963327773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52805923863479886642218515 79208885795219829963327773)
          ·
            refine ⟨29703332173207436236247915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79208885795219829963327773 29703332173207436236247915)
            ·
              refine ⟨44554998259811154354371873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29703332173207436236247915 44554998259811154354371873)
              ·
                refine ⟨33416248694858365765778905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44554998259811154354371873 33416248694858365765778905)
                ·
                  refine ⟨25062186521143774324334179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33416248694858365765778905 25062186521143774324334179)
                  ·
                    refine ⟨37593279781715661486501269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25062186521143774324334179 37593279781715661486501269)
                    ·
                      refine ⟨1762184989767921632179747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37593279781715661486501269 1762184989767921632179747)
                      ·
                        rfl

theorem cell23_3431843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_3431843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431843 prefixEnd_3431843 := by exact prefixLift 3431843
  have htrace : WordTrace (prefixWord ++ tailWord_3431843) baseStart_3431843 baseEnd_3431843 := by
    simpa [prefixWord, tailWord_3431843, baseEnd_3431843] using wordTrace_append hprefix tailTrace_3431843
  have hstable : (prefixWord ++ tailWord_3431843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431843).length < 2 ^ (prefixWord ++ tailWord_3431843).sum := by decide
  have hdescent : baseEnd_3431843 < baseStart_3431843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431847 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_3431847 : Nat := 118140960795 + 3431847 * 2 ^ 59
def prefixEnd_3431847 : Nat := 4983230072969 + 3 ^ 40 * 3431847 * 2
def baseEnd_3431847 : Nat := 1762187043690539616529729

theorem tailTrace_3431847 : CollatzResearch.WordTrace tailWord_3431847 prefixEnd_3431847 1762187043690539616529729 := by
  unfold tailWord_3431847
  simp only [CollatzResearch.WordTrace]
  refine ⟨125169743198011906649885795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83446495465341271099923863 125169743198011906649885795)
  ·
    refine ⟨187754614797017859974828693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125169743198011906649885795 187754614797017859974828693)
    ·
      refine ⟨8800997568610212186320095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 187754614797017859974828693 8800997568610212186320095)
      ·
        refine ⟨13201496352915318279480143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8800997568610212186320095 13201496352915318279480143)
        ·
          refine ⟨19802244529372977419220215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13201496352915318279480143 19802244529372977419220215)
          ·
            refine ⟨29703366794059466128830323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19802244529372977419220215 29703366794059466128830323)
            ·
              refine ⟨44555050191089199193245485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29703366794059466128830323 44555050191089199193245485)
              ·
                refine ⟨16708143821658449697467057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44555050191089199193245485 16708143821658449697467057)
                ·
                  refine ⟨12531107866243837273100293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16708143821658449697467057 12531107866243837273100293)
                  ·
                    refine ⟨2349582724920719488706305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12531107866243837273100293 2349582724920719488706305)
                    ·
                      refine ⟨1762187043690539616529729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349582724920719488706305 1762187043690539616529729)
                      ·
                        rfl

theorem cell23_3431847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_3431847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431847 prefixEnd_3431847 := by exact prefixLift 3431847
  have htrace : WordTrace (prefixWord ++ tailWord_3431847) baseStart_3431847 baseEnd_3431847 := by
    simpa [prefixWord, tailWord_3431847, baseEnd_3431847] using wordTrace_append hprefix tailTrace_3431847
  have hstable : (prefixWord ++ tailWord_3431847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431847).length < 2 ^ (prefixWord ++ tailWord_3431847).sum := by decide
  have hdescent : baseEnd_3431847 < baseStart_3431847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431930 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_3431930 : Nat := 118140960795 + 3431930 * 2 ^ 59
def prefixEnd_3431930 : Nat := 4983230072969 + 3 ^ 40 * 3431930 * 2
def baseEnd_3431930 : Nat := 587409887528287597263949

theorem tailTrace_3431930 : CollatzResearch.WordTrace tailWord_3431930 prefixEnd_3431930 587409887528287597263949 := by
  unfold tailWord_3431930
  simp only [CollatzResearch.WordTrace]
  refine ⟨31293192614177802956289311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83448513637807474550104829 31293192614177802956289311)
  ·
    refine ⟨46939788921266704434433967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31293192614177802956289311 46939788921266704434433967)
    ·
      refine ⟨70409683381900056651650951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46939788921266704434433967 70409683381900056651650951)
      ·
        refine ⟨105614525072850084977476427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70409683381900056651650951 105614525072850084977476427)
        ·
          refine ⟨158421787609275127466214641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105614525072850084977476427 158421787609275127466214641)
          ·
            refine ⟨118816340706956345599660981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158421787609275127466214641 118816340706956345599660981)
            ·
              refine ⟨11139031941277157399968217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118816340706956345599660981 11139031941277157399968217)
              ·
                refine ⟨8354273955957868049976163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11139031941277157399968217 8354273955957868049976163)
                ·
                  refine ⟨12531410933936802074964245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8354273955957868049976163 12531410933936802074964245)
                  ·
                    refine ⟨587409887528287597263949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12531410933936802074964245 587409887528287597263949)
                    ·
                      rfl

theorem cell23_3431930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_3431930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431930 prefixEnd_3431930 := by exact prefixLift 3431930
  have htrace : WordTrace (prefixWord ++ tailWord_3431930) baseStart_3431930 baseEnd_3431930 := by
    simpa [prefixWord, tailWord_3431930, baseEnd_3431930] using wordTrace_append hprefix tailTrace_3431930
  have hstable : (prefixWord ++ tailWord_3431930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431930).length < 2 ^ (prefixWord ++ tailWord_3431930).sum := by decide
  have hdescent : baseEnd_3431930 < baseStart_3431930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431957 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_3431957 : Nat := 118140960795 + 3431957 * 2 ^ 59
def prefixEnd_3431957 : Nat := 4983230072969 + 3 ^ 40 * 3431957 * 2
def baseEnd_3431957 : Nat := 1762243526562534186154223

theorem tailTrace_3431957 : CollatzResearch.WordTrace tailWord_3431957 prefixEnd_3431957 1762243526562534186154223 := by
  unfold tailWord_3431957
  simp only [CollatzResearch.WordTrace]
  refine ⟨125173755227613395436390125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83449170151742263624260083 125173755227613395436390125)
  ·
    refine ⟨46940158210355023288646297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125173755227613395436390125 46940158210355023288646297)
    ·
      refine ⟨35205118657766267466484723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46940158210355023288646297 35205118657766267466484723)
      ·
        refine ⟨52807677986649401199727085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35205118657766267466484723 52807677986649401199727085)
        ·
          refine ⟨19802879244993525449897657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52807677986649401199727085 19802879244993525449897657)
          ·
            refine ⟨14852159433745144087423243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19802879244993525449897657 14852159433745144087423243)
            ·
              refine ⟨22278239150617716131134865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14852159433745144087423243 22278239150617716131134865)
              ·
                refine ⟨16708679362963287098351149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22278239150617716131134865 16708679362963287098351149)
                ·
                  refine ⟨6265754761111232661881681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16708679362963287098351149 6265754761111232661881681)
                  ·
                    refine ⟨4699316070833424496411261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6265754761111232661881681 4699316070833424496411261)
                    ·
                      refine ⟨1762243526562534186154223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4699316070833424496411261 1762243526562534186154223)
                      ·
                        rfl

theorem cell23_3431957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_3431957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431957 prefixEnd_3431957 := by exact prefixLift 3431957
  have htrace : WordTrace (prefixWord ++ tailWord_3431957) baseStart_3431957 baseEnd_3431957 := by
    simpa [prefixWord, tailWord_3431957, baseEnd_3431957] using wordTrace_append hprefix tailTrace_3431957
  have hstable : (prefixWord ++ tailWord_3431957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431957).length < 2 ^ (prefixWord ++ tailWord_3431957).sum := by decide
  have hdescent : baseEnd_3431957 < baseStart_3431957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431971 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 3, 2, 2]
def baseStart_3431971 : Nat := 118140960795 + 3431971 * 2 ^ 59
def prefixEnd_3431971 : Nat := 4983230072969 + 3 ^ 40 * 3431971 * 2
def baseEnd_3431971 : Nat := 1762250715291697131379159

theorem tailTrace_3431971 : CollatzResearch.WordTrace tailWord_3431971 prefixEnd_3431971 1762250715291697131379159 := by
  unfold tailWord_3431971
  simp only [CollatzResearch.WordTrace]
  refine ⟨125174265849562675827399767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83449510566375117218266511 125174265849562675827399767)
  ·
    refine ⟨187761398774344013741099651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125174265849562675827399767 187761398774344013741099651)
    ·
      refine ⟨281642098161516020611649477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187761398774344013741099651 281642098161516020611649477)
      ·
        refine ⟨52807893405284253864684277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281642098161516020611649477 52807893405284253864684277)
        ·
          refine ⟨4950740006745398799814151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52807893405284253864684277 4950740006745398799814151)
          ·
            refine ⟨7426110010118098199721227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950740006745398799814151 7426110010118098199721227)
            ·
              refine ⟨11139165015177147299581841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426110010118098199721227 11139165015177147299581841)
              ·
                refine ⟨8354373761382860474686381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11139165015177147299581841 8354373761382860474686381)
                ·
                  refine ⟨3132890160518572678007393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8354373761382860474686381 3132890160518572678007393)
                  ·
                    refine ⟨2349667620388929508505545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3132890160518572678007393 2349667620388929508505545)
                    ·
                      refine ⟨1762250715291697131379159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349667620388929508505545 1762250715291697131379159)
                      ·
                        rfl

theorem cell23_3431971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_3431971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431971 prefixEnd_3431971 := by exact prefixLift 3431971
  have htrace : WordTrace (prefixWord ++ tailWord_3431971) baseStart_3431971 baseEnd_3431971 := by
    simpa [prefixWord, tailWord_3431971, baseEnd_3431971] using wordTrace_append hprefix tailTrace_3431971
  have hstable : (prefixWord ++ tailWord_3431971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431971).length < 2 ^ (prefixWord ++ tailWord_3431971).sum := by decide
  have hdescent : baseEnd_3431971 < baseStart_3431971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431987 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 3]
def baseStart_3431987 : Nat := 118140960795 + 3431987 * 2 ^ 59
def prefixEnd_3431987 : Nat := 4983230072969 + 3 ^ 40 * 3431987 * 2
def baseEnd_3431987 : Nat := 1762258930982169068779085

theorem tailTrace_3431987 : CollatzResearch.WordTrace tailWord_3431987 prefixEnd_3431987 1762258930982169068779085 := by
  unfold tailWord_3431987
  simp only [CollatzResearch.WordTrace]
  refine ⟨125174849417504710559982215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83449899611669807039988143 125174849417504710559982215)
  ·
    refine ⟨187762274126257065839973323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125174849417504710559982215 187762274126257065839973323)
    ·
      refine ⟨281643411189385598759959985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187762274126257065839973323 281643411189385598759959985)
      ·
        refine ⟨211232558392039199069969989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281643411189385598759959985 211232558392039199069969989)
        ·
          refine ⟨39606104698507349825619373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211232558392039199069969989 39606104698507349825619373)
          ·
            refine ⟨14852289261940256184607265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39606104698507349825619373 14852289261940256184607265)
            ·
              refine ⟨11139216946455192138455449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14852289261940256184607265 11139216946455192138455449)
              ·
                refine ⟨8354412709841394103841587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11139216946455192138455449 8354412709841394103841587)
                ·
                  refine ⟨12531619064762091155762381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8354412709841394103841587 12531619064762091155762381)
                  ·
                    refine ⟨4699357149285784183410893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12531619064762091155762381 4699357149285784183410893)
                    ·
                      refine ⟨1762258930982169068779085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4699357149285784183410893 1762258930982169068779085)
                      ·
                        rfl

theorem cell23_3431987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 3].length) (baseStart_3431987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431987 prefixEnd_3431987 := by exact prefixLift 3431987
  have htrace : WordTrace (prefixWord ++ tailWord_3431987) baseStart_3431987 baseEnd_3431987 := by
    simpa [prefixWord, tailWord_3431987, baseEnd_3431987] using wordTrace_append hprefix tailTrace_3431987
  have hstable : (prefixWord ++ tailWord_3431987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431987).length < 2 ^ (prefixWord ++ tailWord_3431987).sum := by decide
  have hdescent : baseEnd_3431987 < baseStart_3431987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431991 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 1, 2, 3]
def baseStart_3431991 : Nat := 118140960795 + 3431991 * 2 ^ 59
def prefixEnd_3431991 : Nat := 4983230072969 + 3 ^ 40 * 3431991 * 2
def baseEnd_3431991 : Nat := 1762260984904787053129067

theorem tailTrace_3431991 : CollatzResearch.WordTrace tailWord_3431991 prefixEnd_3431991 1762260984904787053129067 := by
  unfold tailWord_3431991
  simp only [CollatzResearch.WordTrace]
  refine ⟨125174995309490219243127827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83449996872993479495418551 125174995309490219243127827)
  ·
    refine ⟨187762492964235328864691741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125174995309490219243127827 187762492964235328864691741)
    ·
      refine ⟨70410934861588248324259403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187762492964235328864691741 70410934861588248324259403)
      ·
        refine ⟨105616402292382372486389105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70410934861588248324259403 105616402292382372486389105)
        ·
          refine ⟨79212301719286779364791829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105616402292382372486389105 79212301719286779364791829)
          ·
            refine ⟨3713076643091567782724617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79212301719286779364791829 3713076643091567782724617)
            ·
              refine ⟨2784807482318675837043463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3713076643091567782724617 2784807482318675837043463)
              ·
                refine ⟨4177211223478013755565195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784807482318675837043463 4177211223478013755565195)
                ·
                  refine ⟨6265816835217020633347793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177211223478013755565195 6265816835217020633347793)
                  ·
                    refine ⟨4699362626412765475010845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6265816835217020633347793 4699362626412765475010845)
                    ·
                      refine ⟨1762260984904787053129067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4699362626412765475010845 1762260984904787053129067)
                      ·
                        rfl

theorem cell23_3431991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 2, 3].length) (baseStart_3431991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3431991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3431991 prefixEnd_3431991 := by exact prefixLift 3431991
  have htrace : WordTrace (prefixWord ++ tailWord_3431991) baseStart_3431991 baseEnd_3431991 := by
    simpa [prefixWord, tailWord_3431991, baseEnd_3431991] using wordTrace_append hprefix tailTrace_3431991
  have hstable : (prefixWord ++ tailWord_3431991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431991).length < 2 ^ (prefixWord ++ tailWord_3431991).sum := by decide
  have hdescent : baseEnd_3431991 < baseStart_3431991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432060 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3432060 : Nat := 118140960795 + 3432060 * 2 ^ 59
def prefixEnd_3432060 : Nat := 4983230072969 + 3 ^ 40 * 3432060 * 2
def baseEnd_3432060 : Nat := 1762296415069947283166249

theorem tailTrace_3432060 : CollatzResearch.WordTrace tailWord_3432060 prefixEnd_3432060 1762296415069947283166249 := by
  unfold tailWord_3432060
  simp only [CollatzResearch.WordTrace]
  refine ⟨62588755973120122013694817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83451674630826829351593089 62588755973120122013694817)
  ·
    refine ⟨46941566979840091510271113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62588755973120122013694817 46941566979840091510271113)
    ·
      refine ⟨35206175234880068632703335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46941566979840091510271113 35206175234880068632703335)
      ·
        refine ⟨52809262852320102949055003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35206175234880068632703335 52809262852320102949055003)
        ·
          refine ⟨79213894278480154423582505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52809262852320102949055003 79213894278480154423582505)
          ·
            refine ⟨59410420708860115817686879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79213894278480154423582505 59410420708860115817686879)
            ·
              refine ⟨89115631063290173726530319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59410420708860115817686879 89115631063290173726530319)
              ·
                refine ⟨133673446594935260589795479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89115631063290173726530319 133673446594935260589795479)
                ·
                  refine ⟨200510169892402890884693219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133673446594935260589795479 200510169892402890884693219)
                  ·
                    refine ⟨300765254838604336327039829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200510169892402890884693219 300765254838604336327039829)
                    ·
                      refine ⟨1762296415069947283166249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 300765254838604336327039829 1762296415069947283166249)
                      ·
                        rfl

theorem cell23_3432060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3432060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432060 prefixEnd_3432060 := by exact prefixLift 3432060
  have htrace : WordTrace (prefixWord ++ tailWord_3432060) baseStart_3432060 baseEnd_3432060 := by
    simpa [prefixWord, tailWord_3432060, baseEnd_3432060] using wordTrace_append hprefix tailTrace_3432060
  have hstable : (prefixWord ++ tailWord_3432060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432060).length < 2 ^ (prefixWord ++ tailWord_3432060).sum := by decide
  have hdescent : baseEnd_3432060 < baseStart_3432060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432061 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 4, 2, 2]
def baseStart_3432061 : Nat := 118140960795 + 3432061 * 2 ^ 59
def prefixEnd_3432061 : Nat := 4983230072969 + 3 ^ 40 * 3432061 * 2
def baseEnd_3432061 : Nat := 1762296928550601779253745

theorem tailTrace_3432061 : CollatzResearch.WordTrace tailWord_3432061 prefixEnd_3432061 1762296928550601779253745 := by
  unfold tailWord_3432061
  simp only [CollatzResearch.WordTrace]
  refine ⟨125177548419236621198176037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83451698946157747465450691 125177548419236621198176037)
  ·
    refine ⟨23470790328606866474658007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125177548419236621198176037 23470790328606866474658007)
    ·
      refine ⟨35206185492910299711987011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23470790328606866474658007 35206185492910299711987011)
      ·
        refine ⟨52809278239365449567980517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35206185492910299711987011 52809278239365449567980517)
        ·
          refine ⟨9901739669881021793996347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52809278239365449567980517 9901739669881021793996347)
          ·
            refine ⟨14852609504821532690994521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9901739669881021793996347 14852609504821532690994521)
            ·
              refine ⟨11139457128616149518245891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14852609504821532690994521 11139457128616149518245891)
              ·
                refine ⟨16709185692924224277368837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11139457128616149518245891 16709185692924224277368837)
                ·
                  refine ⟨3132972317423292052006657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16709185692924224277368837 3132972317423292052006657)
                  ·
                    refine ⟨2349729238067469039004993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3132972317423292052006657 2349729238067469039004993)
                    ·
                      refine ⟨1762296928550601779253745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349729238067469039004993 1762296928550601779253745)
                      ·
                        rfl

theorem cell23_3432061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_3432061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432061 prefixEnd_3432061 := by exact prefixLift 3432061
  have htrace : WordTrace (prefixWord ++ tailWord_3432061) baseStart_3432061 baseEnd_3432061 := by
    simpa [prefixWord, tailWord_3432061, baseEnd_3432061] using wordTrace_append hprefix tailTrace_3432061
  have hstable : (prefixWord ++ tailWord_3432061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432061).length < 2 ^ (prefixWord ++ tailWord_3432061).sum := by decide
  have hdescent : baseEnd_3432061 < baseStart_3432061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432072 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3432072 : Nat := 118140960795 + 3432072 * 2 ^ 59
def prefixEnd_3432072 : Nat := 4983230072969 + 3 ^ 40 * 3432072 * 2
def baseEnd_3432072 : Nat := 1762302576837801236216195

theorem tailTrace_3432072 : CollatzResearch.WordTrace tailWord_3432072 prefixEnd_3432072 1762302576837801236216195 := by
  unfold tailWord_3432072
  simp only [CollatzResearch.WordTrace]
  refine ⟨62588974811098385038413235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83451966414797846717884313 62588974811098385038413235)
  ·
    refine ⟨93883462216647577557619853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62588974811098385038413235 93883462216647577557619853)
    ·
      refine ⟨35206298331242841584107445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93883462216647577557619853 35206298331242841584107445)
      ·
        refine ⟨3300590468554016398510073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35206298331242841584107445 3300590468554016398510073)
        ·
          refine ⟨2475442851415512298882555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3300590468554016398510073 2475442851415512298882555)
          ·
            refine ⟨3713164277123268448323833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475442851415512298882555 3713164277123268448323833)
            ·
              refine ⟨2784873207842451336242875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3713164277123268448323833 2784873207842451336242875)
              ·
                refine ⟨4177309811763677004364313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784873207842451336242875 4177309811763677004364313)
                ·
                  refine ⟨3132982358822757753273235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4177309811763677004364313 3132982358822757753273235)
                  ·
                    refine ⟨4699473538234136629909853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3132982358822757753273235 4699473538234136629909853)
                    ·
                      refine ⟨1762302576837801236216195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4699473538234136629909853 1762302576837801236216195)
                      ·
                        rfl

theorem cell23_3432072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3432072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432072 prefixEnd_3432072 := by exact prefixLift 3432072
  have htrace : WordTrace (prefixWord ++ tailWord_3432072) baseStart_3432072 baseEnd_3432072 := by
    simpa [prefixWord, tailWord_3432072, baseEnd_3432072] using wordTrace_append hprefix tailTrace_3432072
  have hstable : (prefixWord ++ tailWord_3432072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432072).length < 2 ^ (prefixWord ++ tailWord_3432072).sum := by decide
  have hdescent : baseEnd_3432072 < baseStart_3432072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432078 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2]
def baseStart_3432078 : Nat := 118140960795 + 3432078 * 2 ^ 59
def prefixEnd_3432078 : Nat := 4983230072969 + 3 ^ 40 * 3432078 * 2
def baseEnd_3432078 : Nat := 1762305657721728212741167

theorem tailTrace_3432078 : CollatzResearch.WordTrace tailWord_3432078 prefixEnd_3432078 1762305657721728212741167 := by
  unfold tailWord_3432078
  simp only [CollatzResearch.WordTrace]
  refine ⟨15647271057521879137693111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83452112306783355401029925 15647271057521879137693111)
  ·
    refine ⟨23470906586282818706539667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15647271057521879137693111 23470906586282818706539667)
    ·
      refine ⟨35206359879424228059809501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23470906586282818706539667 35206359879424228059809501)
      ·
        refine ⟨13202384954784085522428563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35206359879424228059809501 13202384954784085522428563)
        ·
          refine ⟨19803577432176128283642845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13202384954784085522428563 19803577432176128283642845)
          ·
            refine ⟨7426341537066048106366067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19803577432176128283642845 7426341537066048106366067)
            ·
              refine ⟨11139512305599072159549101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426341537066048106366067 11139512305599072159549101)
              ·
                refine ⟨4177317114599652059830913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11139512305599072159549101 4177317114599652059830913)
                ·
                  refine ⟨3132987835949739044873185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4177317114599652059830913 3132987835949739044873185)
                  ·
                    refine ⟨2349740876962304283654889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3132987835949739044873185 2349740876962304283654889)
                    ·
                      refine ⟨1762305657721728212741167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349740876962304283654889 1762305657721728212741167)
                      ·
                        rfl

theorem cell23_3432078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_3432078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432078 prefixEnd_3432078 := by exact prefixLift 3432078
  have htrace : WordTrace (prefixWord ++ tailWord_3432078) baseStart_3432078 baseEnd_3432078 := by
    simpa [prefixWord, tailWord_3432078, baseEnd_3432078] using wordTrace_append hprefix tailTrace_3432078
  have hstable : (prefixWord ++ tailWord_3432078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432078).length < 2 ^ (prefixWord ++ tailWord_3432078).sum := by decide
  have hdescent : baseEnd_3432078 < baseStart_3432078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432080 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 3, 7]
def baseStart_3432080 : Nat := 118140960795 + 3432080 * 2 ^ 59
def prefixEnd_3432080 : Nat := 4983230072969 + 3 ^ 40 * 3432080 * 2
def baseEnd_3432080 : Nat := 587435561561012401638719

theorem tailTrace_3432080 : CollatzResearch.WordTrace tailWord_3432080 prefixEnd_3432080 587435561561012401638719 := by
  unfold tailWord_3432080
  simp only [CollatzResearch.WordTrace]
  refine ⟨62589120703083893721558847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83452160937445191628745129 62589120703083893721558847)
  ·
    refine ⟨93883681054625840582338271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62589120703083893721558847 93883681054625840582338271)
    ·
      refine ⟨140825521581938760873507407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93883681054625840582338271 140825521581938760873507407)
      ·
        refine ⟨211238282372908141310261111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140825521581938760873507407 211238282372908141310261111)
        ·
          refine ⟨316857423559362211965391667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211238282372908141310261111 316857423559362211965391667)
          ·
            refine ⟨475286135339043317948087501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316857423559362211965391667 475286135339043317948087501)
            ·
              refine ⟨178232300752141244230532813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475286135339043317948087501 178232300752141244230532813)
              ·
                refine ⟨66837112782052966586449805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178232300752141244230532813 66837112782052966586449805)
                ·
                  refine ⟨25063917293269862469918677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66837112782052966586449805 25063917293269862469918677)
                  ·
                    refine ⟨587435561561012401638719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25063917293269862469918677 587435561561012401638719)
                    ·
                      rfl

theorem cell23_3432080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_3432080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432080 prefixEnd_3432080 := by exact prefixLift 3432080
  have htrace : WordTrace (prefixWord ++ tailWord_3432080) baseStart_3432080 baseEnd_3432080 := by
    simpa [prefixWord, tailWord_3432080, baseEnd_3432080] using wordTrace_append hprefix tailTrace_3432080
  have hstable : (prefixWord ++ tailWord_3432080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432080).length < 2 ^ (prefixWord ++ tailWord_3432080).sum := by decide
  have hdescent : baseEnd_3432080 < baseStart_3432080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432118 : List Nat := [5, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_3432118 : Nat := 118140960795 + 3432118 * 2 ^ 59
def prefixEnd_3432118 : Nat := 4983230072969 + 3 ^ 40 * 3432118 * 2
def baseEnd_3432118 : Nat := 195814021883100895137887

theorem tailTrace_3432118 : CollatzResearch.WordTrace tailWord_3432118 prefixEnd_3432118 195814021883100895137887 := by
  unfold tailWord_3432118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7823726711251882495812563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83453084920020079955334005 7823726711251882495812563)
  ·
    refine ⟨11735590066877823743718845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7823726711251882495812563 11735590066877823743718845)
    ·
      refine ⟨4400846275079183903894567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11735590066877823743718845 4400846275079183903894567)
      ·
        refine ⟨6601269412618775855841851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4400846275079183903894567 6601269412618775855841851)
        ·
          refine ⟨9901904118928163783762777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6601269412618775855841851 9901904118928163783762777)
          ·
            refine ⟨7426428089196122837822083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9901904118928163783762777 7426428089196122837822083)
            ·
              refine ⟨11139642133794184256733125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426428089196122837822083 11139642133794184256733125)
              ·
                refine ⟨2088682900086409548137461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11139642133794184256733125 2088682900086409548137461)
                ·
                  refine ⟨195814021883100895137887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2088682900086409548137461 195814021883100895137887)
                  ·
                    rfl

theorem cell23_3432118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_3432118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432118 prefixEnd_3432118 := by exact prefixLift 3432118
  have htrace : WordTrace (prefixWord ++ tailWord_3432118) baseStart_3432118 baseEnd_3432118 := by
    simpa [prefixWord, tailWord_3432118, baseEnd_3432118] using wordTrace_append hprefix tailTrace_3432118
  have hstable : (prefixWord ++ tailWord_3432118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432118).length < 2 ^ (prefixWord ++ tailWord_3432118).sum := by decide
  have hdescent : baseEnd_3432118 < baseStart_3432118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432154 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3]
def baseStart_3432154 : Nat := 118140960795 + 3432154 * 2 ^ 59
def prefixEnd_3432154 : Nat := 4983230072969 + 3 ^ 40 * 3432154 * 2
def baseEnd_3432154 : Nat := 1762344682251469915390817

theorem tailTrace_3432154 : CollatzResearch.WordTrace tailWord_3432154 prefixEnd_3432154 1762344682251469915390817 := by
  unfold tailWord_3432154
  simp only [CollatzResearch.WordTrace]
  refine ⟨31295235101974924520327879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83453960271933132054207677 31295235101974924520327879)
  ·
    refine ⟨46942852652962386780491819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31295235101974924520327879 46942852652962386780491819)
    ·
      refine ⟨70414278979443580170737729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46942852652962386780491819 70414278979443580170737729)
      ·
        refine ⟨52810709234582685128053297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70414278979443580170737729 52810709234582685128053297)
        ·
          refine ⟨39608031925937013846039973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52810709234582685128053297 39608031925937013846039973)
          ·
            refine ⟨7426505986113190096132495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39608031925937013846039973 7426505986113190096132495)
            ·
              refine ⟨11139758979169785144198743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426505986113190096132495 11139758979169785144198743)
              ·
                refine ⟨16709638468754677716298115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11139758979169785144198743 16709638468754677716298115)
                ·
                  refine ⟨25064457703132016574447173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16709638468754677716298115 25064457703132016574447173)
                  ·
                    refine ⟨4699585819337253107708845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25064457703132016574447173 4699585819337253107708845)
                    ·
                      refine ⟨1762344682251469915390817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4699585819337253107708845 1762344682251469915390817)
                      ·
                        rfl

theorem cell23_3432154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_3432154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432154 prefixEnd_3432154 := by exact prefixLift 3432154
  have htrace : WordTrace (prefixWord ++ tailWord_3432154) baseStart_3432154 baseEnd_3432154 := by
    simpa [prefixWord, tailWord_3432154, baseEnd_3432154] using wordTrace_append hprefix tailTrace_3432154
  have hstable : (prefixWord ++ tailWord_3432154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432154).length < 2 ^ (prefixWord ++ tailWord_3432154).sum := by decide
  have hdescent : baseEnd_3432154 < baseStart_3432154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432177 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_3432177 : Nat := 118140960795 + 3432177 * 2 ^ 59
def prefixEnd_3432177 : Nat := 4983230072969 + 3 ^ 40 * 3432177 * 2
def baseEnd_3432177 : Nat := 1762356492306523325403211

theorem tailTrace_3432177 : CollatzResearch.WordTrace tailWord_3432177 prefixEnd_3432177 1762356492306523325403211 := by
  unfold tailWord_3432177
  simp only [CollatzResearch.WordTrace]
  refine ⟨125181779286816373009398785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83454519524544248672932523 125181779286816373009398785)
  ·
    refine ⟨93886334465112279757049089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125181779286816373009398785 93886334465112279757049089)
    ·
      refine ⟨70414750848834209817786817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93886334465112279757049089 70414750848834209817786817)
      ·
        refine ⟨52811063136625657363340113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70414750848834209817786817 52811063136625657363340113)
        ·
          refine ⟨39608297352469243022505085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52811063136625657363340113 39608297352469243022505085)
          ·
            refine ⟨14853111507175966133439407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39608297352469243022505085 14853111507175966133439407)
            ·
              refine ⟨22279667260763949200159111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14853111507175966133439407 22279667260763949200159111)
              ·
                refine ⟨33419500891145923800238667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22279667260763949200159111 33419500891145923800238667)
                ·
                  refine ⟨50129251336718885700358001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33419500891145923800238667 50129251336718885700358001)
                  ·
                    refine ⟨37596938502539164275268501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50129251336718885700358001 37596938502539164275268501)
                    ·
                      refine ⟨1762356492306523325403211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37596938502539164275268501 1762356492306523325403211)
                      ·
                        rfl

theorem cell23_3432177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_3432177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432177 prefixEnd_3432177 := by exact prefixLift 3432177
  have htrace : WordTrace (prefixWord ++ tailWord_3432177) baseStart_3432177 baseEnd_3432177 := by
    simpa [prefixWord, tailWord_3432177, baseEnd_3432177] using wordTrace_append hprefix tailTrace_3432177
  have hstable : (prefixWord ++ tailWord_3432177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432177).length < 2 ^ (prefixWord ++ tailWord_3432177).sum := by decide
  have hdescent : baseEnd_3432177 < baseStart_3432177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432187 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 3, 5]
def baseStart_3432187 : Nat := 118140960795 + 3432187 * 2 ^ 59
def prefixEnd_3432187 : Nat := 4983230072969 + 3 ^ 40 * 3432187 * 2
def baseEnd_3432187 : Nat := 587453875704356095426055

theorem tailTrace_3432187 : CollatzResearch.WordTrace tailWord_3432187 prefixEnd_3432187 587453875704356095426055 := by
  unfold tailWord_3432187
  simp only [CollatzResearch.WordTrace]
  refine ⟨125182144016780144717262815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83454762677853429811508543 125182144016780144717262815)
  ·
    refine ⟨187773216025170217075894223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125182144016780144717262815 187773216025170217075894223)
    ·
      refine ⟨281659824037755325613841335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187773216025170217075894223 281659824037755325613841335)
      ·
        refine ⟨422489736056632988420762003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281659824037755325613841335 422489736056632988420762003)
        ·
          refine ⟨633734604084949482631143005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422489736056632988420762003 633734604084949482631143005)
          ·
            refine ⟨237650476531856055986678627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 633734604084949482631143005 237650476531856055986678627)
            ·
              refine ⟨356475714797784083980017941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237650476531856055986678627 356475714797784083980017941)
              ·
                refine ⟨16709799131146128936563341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 356475714797784083980017941 16709799131146128936563341)
                ·
                  refine ⟨6266174674179798351211253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16709799131146128936563341 6266174674179798351211253)
                  ·
                    refine ⟨587453875704356095426055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6266174674179798351211253 587453875704356095426055)
                    ·
                      rfl

theorem cell23_3432187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 5].length) (baseStart_3432187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432187 prefixEnd_3432187 := by exact prefixLift 3432187
  have htrace : WordTrace (prefixWord ++ tailWord_3432187) baseStart_3432187 baseEnd_3432187 := by
    simpa [prefixWord, tailWord_3432187, baseEnd_3432187] using wordTrace_append hprefix tailTrace_3432187
  have hstable : (prefixWord ++ tailWord_3432187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432187).length < 2 ^ (prefixWord ++ tailWord_3432187).sum := by decide
  have hdescent : baseEnd_3432187 < baseStart_3432187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432194 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3432194 : Nat := 118140960795 + 3432194 * 2 ^ 59
def prefixEnd_3432194 : Nat := 4983230072969 + 3 ^ 40 * 3432194 * 2
def baseEnd_3432194 : Nat := 1762365221477649758890633

theorem tailTrace_3432194 : CollatzResearch.WordTrace tailWord_3432194 prefixEnd_3432194 1762365221477649758890633 := by
  unfold tailWord_3432194
  simp only [CollatzResearch.WordTrace]
  refine ⟨31295599831938696228191909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83454932885169856608511757 31295599831938696228191909)
  ·
    refine ⟨5867924968488505542785983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31295599831938696228191909 5867924968488505542785983)
    ·
      refine ⟨8801887452732758314178975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5867924968488505542785983 8801887452732758314178975)
      ·
        refine ⟨13202831179099137471268463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801887452732758314178975 13202831179099137471268463)
        ·
          refine ⟨19804246768648706206902695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13202831179099137471268463 19804246768648706206902695)
          ·
            refine ⟨29706370152973059310354043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19804246768648706206902695 29706370152973059310354043)
            ·
              refine ⟨44559555229459588965531065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29706370152973059310354043 44559555229459588965531065)
              ·
                refine ⟨33419666422094691724148299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44559555229459588965531065 33419666422094691724148299)
                ·
                  refine ⟨50129499633142037586222449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33419666422094691724148299 50129499633142037586222449)
                  ·
                    refine ⟨37597124724856528189666837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50129499633142037586222449 37597124724856528189666837)
                    ·
                      refine ⟨1762365221477649758890633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37597124724856528189666837 1762365221477649758890633)
                      ·
                        rfl

theorem cell23_3432194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3432194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432194 prefixEnd_3432194 := by exact prefixLift 3432194
  have htrace : WordTrace (prefixWord ++ tailWord_3432194) baseStart_3432194 baseEnd_3432194 := by
    simpa [prefixWord, tailWord_3432194, baseEnd_3432194] using wordTrace_append hprefix tailTrace_3432194
  have hstable : (prefixWord ++ tailWord_3432194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432194).length < 2 ^ (prefixWord ++ tailWord_3432194).sum := by decide
  have hdescent : baseEnd_3432194 < baseStart_3432194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432204 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 1, 5]
def baseStart_3432204 : Nat := 118140960795 + 3432204 * 2 ^ 59
def prefixEnd_3432204 : Nat := 4983230072969 + 3 ^ 40 * 3432204 * 2
def baseEnd_3432204 : Nat := 587456785428064906588529

theorem tailTrace_3432204 : CollatzResearch.WordTrace tailWord_3432204 prefixEnd_3432204 587456785428064906588529 := by
  unfold tailWord_3432204
  simp only [CollatzResearch.WordTrace]
  refine ⟨62591382028859278310315833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83455176038479037747087777 62591382028859278310315833)
  ·
    refine ⟨46943536521644458732736875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62591382028859278310315833 46943536521644458732736875)
    ·
      refine ⟨70415304782466688099105313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46943536521644458732736875 70415304782466688099105313)
      ·
        refine ⟨52811478586850016074328985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70415304782466688099105313 52811478586850016074328985)
        ·
          refine ⟨39608608940137512055746739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52811478586850016074328985 39608608940137512055746739)
          ·
            refine ⟨59412913410206268083620109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39608608940137512055746739 59412913410206268083620109)
            ·
              refine ⟨22279842528827350531357541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59412913410206268083620109 22279842528827350531357541)
              ·
                refine ⟨4177470474155128224629539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22279842528827350531357541 4177470474155128224629539)
                ·
                  refine ⟨6266205711232692336944309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177470474155128224629539 6266205711232692336944309)
                  ·
                    refine ⟨587456785428064906588529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6266205711232692336944309 587456785428064906588529)
                    ·
                      rfl

theorem cell23_3432204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_3432204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432204 prefixEnd_3432204 := by exact prefixLift 3432204
  have htrace : WordTrace (prefixWord ++ tailWord_3432204) baseStart_3432204 baseEnd_3432204 := by
    simpa [prefixWord, tailWord_3432204, baseEnd_3432204] using wordTrace_append hprefix tailTrace_3432204
  have hstable : (prefixWord ++ tailWord_3432204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432204).length < 2 ^ (prefixWord ++ tailWord_3432204).sum := by decide
  have hdescent : baseEnd_3432204 < baseStart_3432204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432228 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 2, 3, 2]
def baseStart_3432228 : Nat := 118140960795 + 3432228 * 2 ^ 59
def prefixEnd_3432228 : Nat := 4983230072969 + 3 ^ 40 * 3432228 * 2
def baseEnd_3432228 : Nat := 1762382679819902625865477

theorem tailTrace_3432228 : CollatzResearch.WordTrace tailWord_3432228 prefixEnd_3432228 1762382679819902625865477 := by
  unfold tailWord_3432228
  simp only [CollatzResearch.WordTrace]
  refine ⟨62591819704815804359752669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83455759606421072479670225 62591819704815804359752669)
  ·
    refine ⟨23471932389305926634907251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62591819704815804359752669 23471932389305926634907251)
    ·
      refine ⟨35207898583958889952360877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23471932389305926634907251 35207898583958889952360877)
      ·
        refine ⟨13202961968984583732135329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35207898583958889952360877 13202961968984583732135329)
        ·
          refine ⟨9902221476738437799101497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13202961968984583732135329 9902221476738437799101497)
          ·
            refine ⟨7426666107553828349326123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9902221476738437799101497 7426666107553828349326123)
            ·
              refine ⟨11139999161330742523989185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426666107553828349326123 11139999161330742523989185)
              ·
                refine ⟨8354999370998056892991889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11139999161330742523989185 8354999370998056892991889)
                ·
                  refine ⟨6266249528248542669743917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8354999370998056892991889 6266249528248542669743917)
                  ·
                    refine ⟨2349843573093203501153969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6266249528248542669743917 2349843573093203501153969)
                    ·
                      refine ⟨1762382679819902625865477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349843573093203501153969 1762382679819902625865477)
                      ·
                        rfl

theorem cell23_3432228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_3432228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432228 prefixEnd_3432228 := by exact prefixLift 3432228
  have htrace : WordTrace (prefixWord ++ tailWord_3432228) baseStart_3432228 baseEnd_3432228 := by
    simpa [prefixWord, tailWord_3432228, baseEnd_3432228] using wordTrace_append hprefix tailTrace_3432228
  have hstable : (prefixWord ++ tailWord_3432228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432228).length < 2 ^ (prefixWord ++ tailWord_3432228).sum := by decide
  have hdescent : baseEnd_3432228 < baseStart_3432228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432262 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_3432262 : Nat := 118140960795 + 3432262 * 2 ^ 59
def prefixEnd_3432262 : Nat := 4983230072969 + 3 ^ 40 * 3432262 * 2
def baseEnd_3432262 : Nat := 1762400138162155492840321

theorem tailTrace_3432262 : CollatzResearch.WordTrace tailWord_3432262 prefixEnd_3432262 1762400138162155492840321 := by
  unfold tailWord_3432262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3912027484109638516445095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83456586327672288350828693 3912027484109638516445095)
  ·
    refine ⟨5868041226164457774667643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3912027484109638516445095 5868041226164457774667643)
    ·
      refine ⟨8802061839246686662001465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5868041226164457774667643 8802061839246686662001465)
      ·
        refine ⟨6601546379435014996501099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8802061839246686662001465 6601546379435014996501099)
        ·
          refine ⟨9902319569152522494751649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6601546379435014996501099 9902319569152522494751649)
          ·
            refine ⟨7426739676864391871063737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9902319569152522494751649 7426739676864391871063737)
            ·
              refine ⟨5570054757648293903297803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7426739676864391871063737 5570054757648293903297803)
              ·
                refine ⟨8355082136472440854946705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5570054757648293903297803 8355082136472440854946705)
                ·
                  refine ⟨6266311602354330641210029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8355082136472440854946705 6266311602354330641210029)
                  ·
                    refine ⟨2349866850882873990453761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6266311602354330641210029 2349866850882873990453761)
                    ·
                      refine ⟨1762400138162155492840321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349866850882873990453761 1762400138162155492840321)
                      ·
                        rfl

theorem cell23_3432262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_3432262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432262 prefixEnd_3432262 := by exact prefixLift 3432262
  have htrace : WordTrace (prefixWord ++ tailWord_3432262) baseStart_3432262 baseEnd_3432262 := by
    simpa [prefixWord, tailWord_3432262, baseEnd_3432262] using wordTrace_append hprefix tailTrace_3432262
  have hstable : (prefixWord ++ tailWord_3432262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432262).length < 2 ^ (prefixWord ++ tailWord_3432262).sum := by decide
  have hdescent : baseEnd_3432262 < baseStart_3432262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432292 : List Nat := [2, 3, 1, 1, 5, 1, 1, 4, 1, 2, 2]
def baseStart_3432292 : Nat := 118140960795 + 3432292 * 2 ^ 59
def prefixEnd_3432292 : Nat := 4983230072969 + 3 ^ 40 * 3432292 * 2
def baseEnd_3432292 : Nat := 1762415542581790375465183

theorem tailTrace_3432292 : CollatzResearch.WordTrace tailWord_3432292 prefixEnd_3432292 1762415542581790375465183 := by
  unfold tailWord_3432292
  simp only [CollatzResearch.WordTrace]
  refine ⟨62592986840699873824917565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83457315787599831766556753 62592986840699873824917565)
  ·
    refine ⟨23472370065262452684344087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62592986840699873824917565 23472370065262452684344087)
    ·
      refine ⟨35208555097893679026516131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23472370065262452684344087 35208555097893679026516131)
      ·
        refine ⟨52812832646840518539774197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35208555097893679026516131 52812832646840518539774197)
        ·
          refine ⟨4951203060641298613103831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52812832646840518539774197 4951203060641298613103831)
          ·
            refine ⟨7426804590961947919655747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4951203060641298613103831 7426804590961947919655747)
            ·
              refine ⟨11140206886442921879483621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426804590961947919655747 11140206886442921879483621)
              ·
                refine ⟨2088788791208047852403179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11140206886442921879483621 2088788791208047852403179)
                ·
                  refine ⟨3133183186812071778604769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088788791208047852403179 3133183186812071778604769)
                  ·
                    refine ⟨2349887390109053833953577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3133183186812071778604769 2349887390109053833953577)
                    ·
                      refine ⟨1762415542581790375465183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349887390109053833953577 1762415542581790375465183)
                      ·
                        rfl

theorem cell23_3432292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_3432292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432292 prefixEnd_3432292 := by exact prefixLift 3432292
  have htrace : WordTrace (prefixWord ++ tailWord_3432292) baseStart_3432292 baseEnd_3432292 := by
    simpa [prefixWord, tailWord_3432292, baseEnd_3432292] using wordTrace_append hprefix tailTrace_3432292
  have hstable : (prefixWord ++ tailWord_3432292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432292).length < 2 ^ (prefixWord ++ tailWord_3432292).sum := by decide
  have hdescent : baseEnd_3432292 < baseStart_3432292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432298 : List Nat := [3, 1, 3, 4, 1, 2, 1, 8]
def baseStart_3432298 : Nat := 118140960795 + 3432298 * 2 ^ 59
def prefixEnd_3432298 : Nat := 4983230072969 + 3 ^ 40 * 3432298 * 2
def baseEnd_3432298 : Nat := 65274763832063605629265

theorem tailTrace_3432298 : CollatzResearch.WordTrace tailWord_3432298 prefixEnd_3432298 65274763832063605629265 := by
  unfold tailWord_3432298
  simp only [CollatzResearch.WordTrace]
  refine ⟨31296548129844502668638387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83457461679585340449702365 31296548129844502668638387)
  ·
    refine ⟨46944822194766754002957581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31296548129844502668638387 46944822194766754002957581)
    ·
      refine ⟨17604308323037532751109093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46944822194766754002957581 17604308323037532751109093)
      ·
        refine ⟨3300807810569537390832955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17604308323037532751109093 3300807810569537390832955)
        ·
          refine ⟨4951211715854306086249433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3300807810569537390832955 4951211715854306086249433)
          ·
            refine ⟨3713408786890729564687075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4951211715854306086249433 3713408786890729564687075)
            ·
              refine ⟨5570113180336094347030613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3713408786890729564687075 5570113180336094347030613)
              ·
                refine ⟨65274763832063605629265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5570113180336094347030613 65274763832063605629265)
                ·
                  rfl

theorem cell23_3432298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 8].length) (baseStart_3432298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432298 prefixEnd_3432298 := by exact prefixLift 3432298
  have htrace : WordTrace (prefixWord ++ tailWord_3432298) baseStart_3432298 baseEnd_3432298 := by
    simpa [prefixWord, tailWord_3432298, baseEnd_3432298] using wordTrace_append hprefix tailTrace_3432298
  have hstable : (prefixWord ++ tailWord_3432298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432298).length < 2 ^ (prefixWord ++ tailWord_3432298).sum := by decide
  have hdescent : baseEnd_3432298 < baseStart_3432298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432384 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 1, 7]
def baseStart_3432384 : Nat := 118140960795 + 3432384 * 2 ^ 59
def prefixEnd_3432384 : Nat := 4983230072969 + 3 ^ 40 * 3432384 * 2
def baseEnd_3432384 : Nat := 587487594267334671838253

theorem tailTrace_3432384 : CollatzResearch.WordTrace tailWord_3432384 prefixEnd_3432384 587487594267334671838253 := by
  unfold tailWord_3432384
  simp only [CollatzResearch.WordTrace]
  refine ⟨62594664598533223681092103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83459552798044298241456137 62594664598533223681092103)
  ·
    refine ⟨93891996897799835521638155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62594664598533223681092103 93891996897799835521638155)
    ·
      refine ⟨140837995346699753282457233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93891996897799835521638155 140837995346699753282457233)
      ·
        refine ⟨105628496510024814961842925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140837995346699753282457233 105628496510024814961842925)
        ·
          refine ⟨39610686191259305610691097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105628496510024814961842925 39610686191259305610691097)
          ·
            refine ⟨29708014643444479208018323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39610686191259305610691097 29708014643444479208018323)
            ·
              refine ⟨44562021965166718812027485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29708014643444479208018323 44562021965166718812027485)
              ·
                refine ⟨16710758236937519554510307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44562021965166718812027485 16710758236937519554510307)
                ·
                  refine ⟨25066137355406279331765461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16710758236937519554510307 25066137355406279331765461)
                  ·
                    refine ⟨587487594267334671838253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25066137355406279331765461 587487594267334671838253)
                    ·
                      rfl

theorem cell23_3432384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_3432384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432384 prefixEnd_3432384 := by exact prefixLift 3432384
  have htrace : WordTrace (prefixWord ++ tailWord_3432384) baseStart_3432384 baseEnd_3432384 := by
    simpa [prefixWord, tailWord_3432384, baseEnd_3432384] using wordTrace_append hprefix tailTrace_3432384
  have hstable : (prefixWord ++ tailWord_3432384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432384).length < 2 ^ (prefixWord ++ tailWord_3432384).sum := by decide
  have hdescent : baseEnd_3432384 < baseStart_3432384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432391 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 1, 7, 2]
def baseStart_3432391 : Nat := 118140960795 + 3432391 * 2 ^ 59
def prefixEnd_3432391 : Nat := 4983230072969 + 3 ^ 40 * 3432391 * 2
def baseEnd_3432391 : Nat := 1762466377166585488127227

theorem tailTrace_3432391 : CollatzResearch.WordTrace tailWord_3432391 prefixEnd_3432391 1762466377166585488127227 := by
  unfold tailWord_3432391
  simp only [CollatzResearch.WordTrace]
  refine ⟨125189584508041087557689027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83459723005360725038459351 125189584508041087557689027)
  ·
    refine ⟨187784376762061631336533541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125189584508041087557689027 187784376762061631336533541)
    ·
      refine ⟨35209570642886555875600039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187784376762061631336533541 35209570642886555875600039)
      ·
        refine ⟨52814355964329833813400059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35209570642886555875600039 52814355964329833813400059)
        ·
          refine ⟨79221533946494750720100089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52814355964329833813400059 79221533946494750720100089)
          ·
            refine ⟨59416150459871063040075067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79221533946494750720100089 59416150459871063040075067)
            ·
              refine ⟨89124225689806594560112601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59416150459871063040075067 89124225689806594560112601)
              ·
                refine ⟨66843169267354945920084451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89124225689806594560112601 66843169267354945920084451)
                ·
                  refine ⟨100264753901032418880126677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66843169267354945920084451 100264753901032418880126677)
                  ·
                    refine ⟨2349955169555447317502969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 100264753901032418880126677 2349955169555447317502969)
                    ·
                      refine ⟨1762466377166585488127227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2349955169555447317502969 1762466377166585488127227)
                      ·
                        rfl

theorem cell23_3432391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_3432391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432391 prefixEnd_3432391 := by exact prefixLift 3432391
  have htrace : WordTrace (prefixWord ++ tailWord_3432391) baseStart_3432391 baseEnd_3432391 := by
    simpa [prefixWord, tailWord_3432391, baseEnd_3432391] using wordTrace_append hprefix tailTrace_3432391
  have hstable : (prefixWord ++ tailWord_3432391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432391).length < 2 ^ (prefixWord ++ tailWord_3432391).sum := by decide
  have hdescent : baseEnd_3432391 < baseStart_3432391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432405 : List Nat := [1, 3, 2, 3, 2, 2, 3, 2, 5]
def baseStart_3432405 : Nat := 118140960795 + 3432405 * 2 ^ 59
def prefixEnd_3432405 : Nat := 4983230072969 + 3 ^ 40 * 3432405 * 2
def baseEnd_3432405 : Nat := 195830396210638714816907

theorem tailTrace_3432405 : CollatzResearch.WordTrace tailWord_3432405 prefixEnd_3432405 195830396210638714816907 := by
  unfold tailWord_3432405
  simp only [CollatzResearch.WordTrace]
  refine ⟨125190095129990367948698669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83460063419993578632465779 125190095129990367948698669)
  ·
    refine ⟨46946285673746387980762001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125190095129990367948698669 46946285673746387980762001)
    ·
      refine ⟨35209714255309790985571501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46946285673746387980762001 35209714255309790985571501)
      ·
        refine ⟨13203642845741171619589313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35209714255309790985571501 13203642845741171619589313)
        ·
          refine ⟨9902732134305878714691985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13203642845741171619589313 9902732134305878714691985)
          ·
            refine ⟨7427049100729409036018989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9902732134305878714691985 7427049100729409036018989)
            ·
              refine ⟨2785143412773528388507121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7427049100729409036018989 2785143412773528388507121)
              ·
                refine ⟨2088857559580146291380341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2785143412773528388507121 2088857559580146291380341)
                ·
                  refine ⟨195830396210638714816907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2088857559580146291380341 195830396210638714816907)
                  ·
                    rfl

theorem cell23_3432405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_3432405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432405 prefixEnd_3432405 := by exact prefixLift 3432405
  have htrace : WordTrace (prefixWord ++ tailWord_3432405) baseStart_3432405 baseEnd_3432405 := by
    simpa [prefixWord, tailWord_3432405, baseEnd_3432405] using wordTrace_append hprefix tailTrace_3432405
  have hstable : (prefixWord ++ tailWord_3432405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432405).length < 2 ^ (prefixWord ++ tailWord_3432405).sum := by decide
  have hdescent : baseEnd_3432405 < baseStart_3432405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432431 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 5, 4]
def baseStart_3432431 : Nat := 118140960795 + 3432431 * 2 ^ 59
def prefixEnd_3432431 : Nat := 4983230072969 + 3 ^ 40 * 3432431 * 2
def baseEnd_3432431 : Nat := 587495638797588443875681

theorem tailTrace_3432431 : CollatzResearch.WordTrace tailWord_3432431 prefixEnd_3432431 587495638797588443875681 := by
  unfold tailWord_3432431
  simp only [CollatzResearch.WordTrace]
  refine ⟨125191043427896174389145147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83460695618597449592763431 125191043427896174389145147)
  ·
    refine ⟨187786565141844261583717721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125191043427896174389145147 187786565141844261583717721)
    ·
      refine ⟨140839923856383196187788291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187786565141844261583717721 140839923856383196187788291)
      ·
        refine ⟨211259885784574794281682437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140839923856383196187788291 211259885784574794281682437)
        ·
          refine ⟨39611228584607773927815457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211259885784574794281682437 39611228584607773927815457)
          ·
            refine ⟨29708421438455830445861593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39611228584607773927815457 29708421438455830445861593)
            ·
              refine ⟨22281316078841872834396195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29708421438455830445861593 22281316078841872834396195)
              ·
                refine ⟨33421974118262809251594293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22281316078841872834396195 33421974118262809251594293)
                ·
                  refine ⟨3133310073587138367336965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33421974118262809251594293 3133310073587138367336965)
                  ·
                    refine ⟨587495638797588443875681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133310073587138367336965 587495638797588443875681)
                    ·
                      rfl

theorem cell23_3432431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 4].length) (baseStart_3432431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432431 prefixEnd_3432431 := by exact prefixLift 3432431
  have htrace : WordTrace (prefixWord ++ tailWord_3432431) baseStart_3432431 baseEnd_3432431 := by
    simpa [prefixWord, tailWord_3432431, baseEnd_3432431] using wordTrace_append hprefix tailTrace_3432431
  have hstable : (prefixWord ++ tailWord_3432431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432431).length < 2 ^ (prefixWord ++ tailWord_3432431).sum := by decide
  have hdescent : baseEnd_3432431 < baseStart_3432431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432464 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_3432464 : Nat := 118140960795 + 3432464 * 2 ^ 59
def prefixEnd_3432464 : Nat := 4983230072969 + 3 ^ 40 * 3432464 * 2
def baseEnd_3432464 : Nat := 1762503861254363702514391

theorem tailTrace_3432464 : CollatzResearch.WordTrace tailWord_3432464 prefixEnd_3432464 1762503861254363702514391 := by
  unfold tailWord_3432464
  simp only [CollatzResearch.WordTrace]
  refine ⟨62596123518388310512548223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83461498024517747350064297 62596123518388310512548223)
  ·
    refine ⟨93894185277582465768822335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62596123518388310512548223 93894185277582465768822335)
    ·
      refine ⟨140841277916373698653233503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93894185277582465768822335 140841277916373698653233503)
      ·
        refine ⟨211261916874560547979850255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140841277916373698653233503 211261916874560547979850255)
        ·
          refine ⟨316892875311840821969775383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211261916874560547979850255 316892875311840821969775383)
          ·
            refine ⟨475339312967761232954663075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316892875311840821969775383 475339312967761232954663075)
            ·
              refine ⟨713008969451641849431994613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475339312967761232954663075 713008969451641849431994613)
              ·
                refine ⟨66844590886091423384249495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 713008969451641849431994613 66844590886091423384249495)
                ·
                  refine ⟨100266886329137135076374243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66844590886091423384249495 100266886329137135076374243)
                  ·
                    refine ⟨150400329493705702614561365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100266886329137135076374243 150400329493705702614561365)
                    ·
                      refine ⟨1762503861254363702514391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 150400329493705702614561365 1762503861254363702514391)
                      ·
                        rfl

theorem cell23_3432464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_3432464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432464 prefixEnd_3432464 := by exact prefixLift 3432464
  have htrace : WordTrace (prefixWord ++ tailWord_3432464) baseStart_3432464 baseEnd_3432464 := by
    simpa [prefixWord, tailWord_3432464, baseEnd_3432464] using wordTrace_append hprefix tailTrace_3432464
  have hstable : (prefixWord ++ tailWord_3432464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432464).length < 2 ^ (prefixWord ++ tailWord_3432464).sum := by decide
  have hdescent : baseEnd_3432464 < baseStart_3432464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432508 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 1, 5]
def baseStart_3432508 : Nat := 118140960795 + 3432508 * 2 ^ 59
def prefixEnd_3432508 : Nat := 4983230072969 + 3 ^ 40 * 3432508 * 2
def baseEnd_3432508 : Nat := 587508818134387176788063

theorem tailTrace_3432508 : CollatzResearch.WordTrace tailWord_3432508 prefixEnd_3432508 587508818134387176788063 := by
  unfold tailWord_3432508
  simp only [CollatzResearch.WordTrace]
  refine ⟨62596925924308608269849089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83462567899078144359798785 62596925924308608269849089)
  ·
    refine ⟨46947694443231456202386817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62596925924308608269849089 46947694443231456202386817)
    ·
      refine ⟨35210770832423592151790113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46947694443231456202386817 35210770832423592151790113)
      ·
        refine ⟨26408078124317694113842585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35210770832423592151790113 26408078124317694113842585)
        ·
          refine ⟨19806058593238270585381939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26408078124317694113842585 19806058593238270585381939)
          ·
            refine ⟨29709087889857405878072909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19806058593238270585381939 29709087889857405878072909)
            ·
              refine ⟨11140907958696527204277341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29709087889857405878072909 11140907958696527204277341)
              ·
                refine ⟨4177840484511197701604003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11140907958696527204277341 4177840484511197701604003)
                ·
                  refine ⟨6266760726766796552406005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177840484511197701604003 6266760726766796552406005)
                  ·
                    refine ⟨587508818134387176788063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6266760726766796552406005 587508818134387176788063)
                    ·
                      rfl

theorem cell23_3432508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_3432508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432508 prefixEnd_3432508 := by exact prefixLift 3432508
  have htrace : WordTrace (prefixWord ++ tailWord_3432508) baseStart_3432508 baseEnd_3432508 := by
    simpa [prefixWord, tailWord_3432508, baseEnd_3432508] using wordTrace_append hprefix tailTrace_3432508
  have hstable : (prefixWord ++ tailWord_3432508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432508).length < 2 ^ (prefixWord ++ tailWord_3432508).sum := by decide
  have hdescent : baseEnd_3432508 < baseStart_3432508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432548 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_3432548 : Nat := 118140960795 + 3432548 * 2 ^ 59
def prefixEnd_3432548 : Nat := 4983230072969 + 3 ^ 40 * 3432548 * 2
def baseEnd_3432548 : Nat := 1762546993629341373864005

theorem tailTrace_3432548 : CollatzResearch.WordTrace tailWord_3432548 prefixEnd_3432548 1762546993629341373864005 := by
  unfold tailWord_3432548
  simp only [CollatzResearch.WordTrace]
  refine ⟨62597655384236151685577149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83463540512314868914102865 62597655384236151685577149)
  ·
    refine ⟨23474120769088556882091431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62597655384236151685577149 23474120769088556882091431)
    ·
      refine ⟨35211181153632835323137147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23474120769088556882091431 35211181153632835323137147)
      ·
        refine ⟨52816771730449252984705721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35211181153632835323137147 52816771730449252984705721)
        ·
          refine ⟨39612578797836939738529291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52816771730449252984705721 39612578797836939738529291)
          ·
            refine ⟨59418868196755409607793937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39612578797836939738529291 59418868196755409607793937)
            ·
              refine ⟨44564151147566557205845453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59418868196755409607793937 44564151147566557205845453)
              ·
                refine ⟨16711556680337458952192045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44564151147566557205845453 16711556680337458952192045)
                ·
                  refine ⟨6266833755126547107072017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16711556680337458952192045 6266833755126547107072017)
                  ·
                    refine ⟨4700125316344910330304013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6266833755126547107072017 4700125316344910330304013)
                    ·
                      refine ⟨1762546993629341373864005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4700125316344910330304013 1762546993629341373864005)
                      ·
                        rfl

theorem cell23_3432548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_3432548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432548 prefixEnd_3432548 := by exact prefixLift 3432548
  have htrace : WordTrace (prefixWord ++ tailWord_3432548) baseStart_3432548 baseEnd_3432548 := by
    simpa [prefixWord, tailWord_3432548, baseEnd_3432548] using wordTrace_append hprefix tailTrace_3432548
  have hstable : (prefixWord ++ tailWord_3432548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432548).length < 2 ^ (prefixWord ++ tailWord_3432548).sum := by decide
  have hdescent : baseEnd_3432548 < baseStart_3432548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432551 : List Nat := [1, 1, 5, 1, 1, 2, 3, 9]
def baseStart_3432551 : Nat := 118140960795 + 3432551 * 2 ^ 59
def prefixEnd_3432551 : Nat := 4983230072969 + 3 ^ 40 * 3432551 * 2
def baseEnd_3432551 : Nat := 65279575335974254152833

theorem tailTrace_3432551 : CollatzResearch.WordTrace tailWord_3432551 prefixEnd_3432551 65279575335974254152833 := by
  unfold tailWord_3432551
  simp only [CollatzResearch.WordTrace]
  refine ⟨125195420187461434883513507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83463613458307623255675671 125195420187461434883513507)
  ·
    refine ⟨187793130281192152325270261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125195420187461434883513507 187793130281192152325270261)
    ·
      refine ⟨17605605963861764280494087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187793130281192152325270261 17605605963861764280494087)
      ·
        refine ⟨26408408945792646420741131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17605605963861764280494087 26408408945792646420741131)
        ·
          refine ⟨39612613418688969631111697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26408408945792646420741131 39612613418688969631111697)
          ·
            refine ⟨29709460064016727223333773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39612613418688969631111697 29709460064016727223333773)
            ·
              refine ⟨11141047524006272708750165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29709460064016727223333773 11141047524006272708750165)
              ·
                refine ⟨65279575335974254152833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11141047524006272708750165 65279575335974254152833)
                ·
                  rfl

theorem cell23_3432551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 9].length) (baseStart_3432551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432551 prefixEnd_3432551 := by exact prefixLift 3432551
  have htrace : WordTrace (prefixWord ++ tailWord_3432551) baseStart_3432551 baseEnd_3432551 := by
    simpa [prefixWord, tailWord_3432551, baseEnd_3432551] using wordTrace_append hprefix tailTrace_3432551
  have hstable : (prefixWord ++ tailWord_3432551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432551).length < 2 ^ (prefixWord ++ tailWord_3432551).sum := by decide
  have hdescent : baseEnd_3432551 < baseStart_3432551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432558 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3432558 : Nat := 118140960795 + 3432558 * 2 ^ 59
def prefixEnd_3432558 : Nat := 4983230072969 + 3 ^ 40 * 3432558 * 2
def baseEnd_3432558 : Nat := 1762552128435886334738959

theorem tailTrace_3432558 : CollatzResearch.WordTrace tailWord_3432558 prefixEnd_3432558 1762552128435886334738959 := by
  unfold tailWord_3432558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15649459437304509384877291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83463783665624050052678885 15649459437304509384877291)
  ·
    refine ⟨23474189155956764077315937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15649459437304509384877291 23474189155956764077315937)
    ·
      refine ⟨17605641866967573057986953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23474189155956764077315937 17605641866967573057986953)
      ·
        refine ⟨13204231400225679793490215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17605641866967573057986953 13204231400225679793490215)
        ·
          refine ⟨19806347100338519690235323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13204231400225679793490215 19806347100338519690235323)
          ·
            refine ⟨29709520650507779535352985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19806347100338519690235323 29709520650507779535352985)
            ·
              refine ⟨22282140487880834651514739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29709520650507779535352985 22282140487880834651514739)
              ·
                refine ⟨33423210731821251977272109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22282140487880834651514739 33423210731821251977272109)
                ·
                  refine ⟨12533704024432969491477041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33423210731821251977272109 12533704024432969491477041)
                  ·
                    refine ⟨9400278018324727118607781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12533704024432969491477041 9400278018324727118607781)
                    ·
                      refine ⟨1762552128435886334738959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9400278018324727118607781 1762552128435886334738959)
                      ·
                        rfl

theorem cell23_3432558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3432558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432558 prefixEnd_3432558 := by exact prefixLift 3432558
  have htrace : WordTrace (prefixWord ++ tailWord_3432558) baseStart_3432558 baseEnd_3432558 := by
    simpa [prefixWord, tailWord_3432558, baseEnd_3432558] using wordTrace_append hprefix tailTrace_3432558
  have hstable : (prefixWord ++ tailWord_3432558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432558).length < 2 ^ (prefixWord ++ tailWord_3432558).sum := by decide
  have hdescent : baseEnd_3432558 < baseStart_3432558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432588 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 1, 9, 2]
def baseStart_3432588 : Nat := 118140960795 + 3432588 * 2 ^ 59
def prefixEnd_3432588 : Nat := 4983230072969 + 3 ^ 40 * 3432588 * 2
def baseEnd_3432588 : Nat := 1762567532855521217363821

theorem tailTrace_3432588 : CollatzResearch.WordTrace tailWord_3432588 prefixEnd_3432588 1762567532855521217363821 := by
  unfold tailWord_3432588
  simp only [CollatzResearch.WordTrace]
  refine ⟨62598384844163695101305209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83464513125551593468406945 62598384844163695101305209)
  ·
    refine ⟨46948788633122771325978907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62598384844163695101305209 46948788633122771325978907)
    ·
      refine ⟨70423182949684156988968361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46948788633122771325978907 70423182949684156988968361)
      ·
        refine ⟨52817387212263117741726271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70423182949684156988968361 52817387212263117741726271)
        ·
          refine ⟨79226080818394676612589407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52817387212263117741726271 79226080818394676612589407)
          ·
            refine ⟨118839121227592014918884111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79226080818394676612589407 118839121227592014918884111)
            ·
              refine ⟨178258681841388022378326167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118839121227592014918884111 178258681841388022378326167)
              ·
                refine ⟨267388022762082033567489251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178258681841388022378326167 267388022762082033567489251)
                ·
                  refine ⟨401082034143123050351233877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267388022762082033567489251 401082034143123050351233877)
                  ·
                    refine ⟨2350090043807361623151761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 401082034143123050351233877 2350090043807361623151761)
                    ·
                      refine ⟨1762567532855521217363821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350090043807361623151761 1762567532855521217363821)
                      ·
                        rfl

theorem cell23_3432588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_3432588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432588 prefixEnd_3432588 := by exact prefixLift 3432588
  have htrace : WordTrace (prefixWord ++ tailWord_3432588) baseStart_3432588 baseEnd_3432588 := by
    simpa [prefixWord, tailWord_3432588, baseEnd_3432588] using wordTrace_append hprefix tailTrace_3432588
  have hstable : (prefixWord ++ tailWord_3432588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432588).length < 2 ^ (prefixWord ++ tailWord_3432588).sum := by decide
  have hdescent : baseEnd_3432588 < baseStart_3432588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432596 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_3432596 : Nat := 118140960795 + 3432596 * 2 ^ 59
def prefixEnd_3432596 : Nat := 4983230072969 + 3 ^ 40 * 3432596 * 2
def baseEnd_3432596 : Nat := 1762571640700757186063785

theorem tailTrace_3432596 : CollatzResearch.WordTrace tailWord_3432596 prefixEnd_3432596 1762571640700757186063785 := by
  unfold tailWord_3432596
  simp only [CollatzResearch.WordTrace]
  refine ⟨62598530736149203784450821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83464707648198938379267761 62598530736149203784450821)
  ·
    refine ⟨11737224513027975709584529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62598530736149203784450821 11737224513027975709584529)
    ·
      refine ⟨8802918384770981782188397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11737224513027975709584529 8802918384770981782188397)
      ·
        refine ⟨3301094394289118168320649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8802918384770981782188397 3301094394289118168320649)
        ·
          refine ⟨2475820795716838626240487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3301094394289118168320649 2475820795716838626240487)
          ·
            refine ⟨3713731193575257939360731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475820795716838626240487 3713731193575257939360731)
            ·
              refine ⟨5570596790362886909041097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3713731193575257939360731 5570596790362886909041097)
              ·
                refine ⟨4177947592772165181780823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5570596790362886909041097 4177947592772165181780823)
                ·
                  refine ⟨6266921389158247772671235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177947592772165181780823 6266921389158247772671235)
                  ·
                    refine ⟨9400382083737371659006853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6266921389158247772671235 9400382083737371659006853)
                    ·
                      refine ⟨1762571640700757186063785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9400382083737371659006853 1762571640700757186063785)
                      ·
                        rfl

theorem cell23_3432596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_3432596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432596 prefixEnd_3432596 := by exact prefixLift 3432596
  have htrace : WordTrace (prefixWord ++ tailWord_3432596) baseStart_3432596 baseEnd_3432596 := by
    simpa [prefixWord, tailWord_3432596, baseEnd_3432596] using wordTrace_append hprefix tailTrace_3432596
  have hstable : (prefixWord ++ tailWord_3432596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432596).length < 2 ^ (prefixWord ++ tailWord_3432596).sum := by decide
  have hdescent : baseEnd_3432596 < baseStart_3432596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432599 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 1, 2, 3]
def baseStart_3432599 : Nat := 118140960795 + 3432599 * 2 ^ 59
def prefixEnd_3432599 : Nat := 4983230072969 + 3 ^ 40 * 3432599 * 2
def baseEnd_3432599 : Nat := 1762573181142720674326271

theorem tailTrace_3432599 : CollatzResearch.WordTrace tailWord_3432599 prefixEnd_3432599 1762573181142720674326271 := by
  unfold tailWord_3432599
  simp only [CollatzResearch.WordTrace]
  refine ⟨125197170891287539081260851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83464780594191692720840567 125197170891287539081260851)
  ·
    refine ⟨187795756336931308621891277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125197170891287539081260851 187795756336931308621891277)
    ·
      refine ⟨70423408626349240733209229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187795756336931308621891277 70423408626349240733209229)
      ·
        refine ⟨26408778234880965274953461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70423408626349240733209229 26408778234880965274953461)
        ·
          refine ⟨2475822959520090494526887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26408778234880965274953461 2475822959520090494526887)
          ·
            refine ⟨3713734439280135741790331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475822959520090494526887 3713734439280135741790331)
            ·
              refine ⟨5570601658920203612685497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3713734439280135741790331 5570601658920203612685497)
              ·
                refine ⟨4177951244190152709514123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5570601658920203612685497 4177951244190152709514123)
                ·
                  refine ⟨6266926866285229064271185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177951244190152709514123 6266926866285229064271185)
                  ·
                    refine ⟨4700195149713921798203389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6266926866285229064271185 4700195149713921798203389)
                    ·
                      refine ⟨1762573181142720674326271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4700195149713921798203389 1762573181142720674326271)
                      ·
                        rfl

theorem cell23_3432599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_3432599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432599 prefixEnd_3432599 := by exact prefixLift 3432599
  have htrace : WordTrace (prefixWord ++ tailWord_3432599) baseStart_3432599 baseEnd_3432599 := by
    simpa [prefixWord, tailWord_3432599, baseEnd_3432599] using wordTrace_append hprefix tailTrace_3432599
  have hstable : (prefixWord ++ tailWord_3432599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432599).length < 2 ^ (prefixWord ++ tailWord_3432599).sum := by decide
  have hdescent : baseEnd_3432599 < baseStart_3432599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432611 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 6, 6]
def baseStart_3432611 : Nat := 118140960795 + 3432611 * 2 ^ 59
def prefixEnd_3432611 : Nat := 4983230072969 + 3 ^ 40 * 3432611 * 2
def baseEnd_3432611 : Nat := 587526447636858209125405

theorem tailTrace_3432611 : CollatzResearch.WordTrace tailWord_3432611 prefixEnd_3432611 587526447636858209125405 := by
  unfold tailWord_3432611
  simp only [CollatzResearch.WordTrace]
  refine ⟨125197608567244065130697687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83465072378162710087131791 125197608567244065130697687)
  ·
    refine ⟨187796412850866097696046531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125197608567244065130697687 187796412850866097696046531)
    ·
      refine ⟨281694619276299146544069797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187796412850866097696046531 281694619276299146544069797)
      ·
        refine ⟨52817741114306089977013087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281694619276299146544069797 52817741114306089977013087)
        ·
          refine ⟨79226611671459134965519631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52817741114306089977013087 79226611671459134965519631)
          ·
            refine ⟨118839917507188702448279447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79226611671459134965519631 118839917507188702448279447)
            ·
              refine ⟨178259876260783053672419171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118839917507188702448279447 178259876260783053672419171)
              ·
                refine ⟨267389814391174580508628757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178259876260783053672419171 267389814391174580508628757)
                ·
                  refine ⟨12533897549586308461341973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 267389814391174580508628757 12533897549586308461341973)
                  ·
                    refine ⟨587526447636858209125405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12533897549586308461341973 587526447636858209125405)
                    ·
                      rfl

theorem cell23_3432611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 6].length) (baseStart_3432611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432611 prefixEnd_3432611 := by exact prefixLift 3432611
  have htrace : WordTrace (prefixWord ++ tailWord_3432611) baseStart_3432611 baseEnd_3432611 := by
    simpa [prefixWord, tailWord_3432611, baseEnd_3432611] using wordTrace_append hprefix tailTrace_3432611
  have hstable : (prefixWord ++ tailWord_3432611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432611).length < 2 ^ (prefixWord ++ tailWord_3432611).sum := by decide
  have hdescent : baseEnd_3432611 < baseStart_3432611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432658 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 9]
def baseStart_3432658 : Nat := 118140960795 + 3432658 * 2 ^ 59
def prefixEnd_3432658 : Nat := 4983230072969 + 3 ^ 40 * 3432658 * 2
def baseEnd_3432658 : Nat := 195844830722370660387611

theorem tailTrace_3432658 : CollatzResearch.WordTrace tailWord_3432658 prefixEnd_3432658 195844830722370660387611 := by
  unfold tailWord_3432658
  simp only [CollatzResearch.WordTrace]
  refine ⟨31299830699518448039414657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83466215198715861438439085 31299830699518448039414657)
  ·
    refine ⟨23474873024638836029560993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31299830699518448039414657 23474873024638836029560993)
    ·
      refine ⟨17606154768479127022170745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23474873024638836029560993 17606154768479127022170745)
      ·
        refine ⟨13204616076359345266628059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17606154768479127022170745 13204616076359345266628059)
        ·
          refine ⟨19806924114539017899942089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13204616076359345266628059 19806924114539017899942089)
          ·
            refine ⟨14855193085904263424956567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19806924114539017899942089 14855193085904263424956567)
            ·
              refine ⟨22282789628856395137434851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14855193085904263424956567 22282789628856395137434851)
              ·
                refine ⟨33424184443284592706152277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22282789628856395137434851 33424184443284592706152277)
                ·
                  refine ⟨195844830722370660387611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33424184443284592706152277 195844830722370660387611)
                  ·
                    rfl

theorem cell23_3432658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_3432658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432658 prefixEnd_3432658 := by exact prefixLift 3432658
  have htrace : WordTrace (prefixWord ++ tailWord_3432658) baseStart_3432658 baseEnd_3432658 := by
    simpa [prefixWord, tailWord_3432658, baseEnd_3432658] using wordTrace_append hprefix tailTrace_3432658
  have hstable : (prefixWord ++ tailWord_3432658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432658).length < 2 ^ (prefixWord ++ tailWord_3432658).sum := by decide
  have hdescent : baseEnd_3432658 < baseStart_3432658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432688 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 2, 5]
def baseStart_3432688 : Nat := 118140960795 + 3432688 * 2 ^ 59
def prefixEnd_3432688 : Nat := 4983230072969 + 3 ^ 40 * 3432688 * 2
def baseEnd_3432688 : Nat := 587539626973656942037787

theorem tailTrace_3432688 : CollatzResearch.WordTrace tailWord_3432688 prefixEnd_3432688 587539626973656942037787 := by
  unfold tailWord_3432688
  simp only [CollatzResearch.WordTrace]
  refine ⟨62600208493982553640625359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83466944658643404854167145 62600208493982553640625359)
  ·
    refine ⟨93900312740973830460938039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62600208493982553640625359 93900312740973830460938039)
    ·
      refine ⟨140850469111460745691407059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93900312740973830460938039 140850469111460745691407059)
      ·
        refine ⟨211275703667191118537110589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140850469111460745691407059 211275703667191118537110589)
        ·
          refine ⟨79228388875196669451416471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211275703667191118537110589 79228388875196669451416471)
          ·
            refine ⟨118842583312795004177124707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79228388875196669451416471 118842583312795004177124707)
            ·
              refine ⟨178263874969192506265687061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118842583312795004177124707 178263874969192506265687061)
              ·
                refine ⟨8356119139180898731204081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178263874969192506265687061 8356119139180898731204081)
                ·
                  refine ⟨6267089354385674048403061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8356119139180898731204081 6267089354385674048403061)
                  ·
                    refine ⟨587539626973656942037787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6267089354385674048403061 587539626973656942037787)
                    ·
                      rfl

theorem cell23_3432688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_3432688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432688 prefixEnd_3432688 := by exact prefixLift 3432688
  have htrace : WordTrace (prefixWord ++ tailWord_3432688) baseStart_3432688 baseEnd_3432688 := by
    simpa [prefixWord, tailWord_3432688, baseEnd_3432688] using wordTrace_append hprefix tailTrace_3432688
  have hstable : (prefixWord ++ tailWord_3432688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432688).length < 2 ^ (prefixWord ++ tailWord_3432688).sum := by decide
  have hdescent : baseEnd_3432688 < baseStart_3432688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432718 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_3432718 : Nat := 118140960795 + 3432718 * 2 ^ 59
def prefixEnd_3432718 : Nat := 4983230072969 + 3 ^ 40 * 3432718 * 2
def baseEnd_3432718 : Nat := 587544761780201902912741

theorem tailTrace_3432718 : CollatzResearch.WordTrace tailWord_3432718 prefixEnd_3432718 587544761780201902912741 := by
  unfold tailWord_3432718
  simp only [CollatzResearch.WordTrace]
  refine ⟨15650188897232052800605351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83467674118570948269895205 15650188897232052800605351)
  ·
    refine ⟨23475283345848079200908027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15650188897232052800605351 23475283345848079200908027)
    ·
      refine ⟨35212925018772118801362041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23475283345848079200908027 35212925018772118801362041)
      ·
        refine ⟨26409693764079089101021531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35212925018772118801362041 26409693764079089101021531)
        ·
          refine ⟨39614540646118633651532297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26409693764079089101021531 39614540646118633651532297)
          ·
            refine ⟨29710905484588975238649223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39614540646118633651532297 29710905484588975238649223)
            ·
              refine ⟨44566358226883462857973835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29710905484588975238649223 44566358226883462857973835)
              ·
                refine ⟨66849537340325194286960753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44566358226883462857973835 66849537340325194286960753)
                ·
                  refine ⟨50137153005243895715220565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66849537340325194286960753 50137153005243895715220565)
                  ·
                    refine ⟨587544761780201902912741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50137153005243895715220565 587544761780201902912741)
                    ·
                      rfl

theorem cell23_3432718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_3432718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432718 prefixEnd_3432718 := by exact prefixLift 3432718
  have htrace : WordTrace (prefixWord ++ tailWord_3432718) baseStart_3432718 baseEnd_3432718 := by
    simpa [prefixWord, tailWord_3432718, baseEnd_3432718] using wordTrace_append hprefix tailTrace_3432718
  have hstable : (prefixWord ++ tailWord_3432718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432718).length < 2 ^ (prefixWord ++ tailWord_3432718).sum := by decide
  have hdescent : baseEnd_3432718 < baseStart_3432718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432725 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 1, 6, 2]
def baseStart_3432725 : Nat := 118140960795 + 3432725 * 2 ^ 59
def prefixEnd_3432725 : Nat := 4983230072969 + 3 ^ 40 * 3432725 * 2
def baseEnd_3432725 : Nat := 1762637879705187181350691

theorem tailTrace_3432725 : CollatzResearch.WordTrace tailWord_3432725 prefixEnd_3432725 1762637879705187181350691 := by
  unfold tailWord_3432725
  simp only [CollatzResearch.WordTrace]
  refine ⟨125201766488831062600347629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83467844325887375066898419 125201766488831062600347629)
  ·
    refine ⟨46950662433311648475130361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125201766488831062600347629 46950662433311648475130361)
    ·
      refine ⟨35212996824983736356347771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46950662433311648475130361 35212996824983736356347771)
      ·
        refine ⟨52819495237475604534521657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35212996824983736356347771 52819495237475604534521657)
        ·
          refine ⟨39614621428106703400891243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52819495237475604534521657 39614621428106703400891243)
          ·
            refine ⟨59421932142160055101336865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39614621428106703400891243 59421932142160055101336865)
            ·
              refine ⟨44566449106620041326002649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59421932142160055101336865 44566449106620041326002649)
              ·
                refine ⟨33424836829965030994501987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44566449106620041326002649 33424836829965030994501987)
                ·
                  refine ⟨50137255244947546491752981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33424836829965030994501987 50137255244947546491752981)
                  ·
                    refine ⟨2350183839606916241800921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50137255244947546491752981 2350183839606916241800921)
                    ·
                      refine ⟨1762637879705187181350691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350183839606916241800921 1762637879705187181350691)
                      ·
                        rfl

theorem cell23_3432725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_3432725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432725 prefixEnd_3432725 := by exact prefixLift 3432725
  have htrace : WordTrace (prefixWord ++ tailWord_3432725) baseStart_3432725 baseEnd_3432725 := by
    simpa [prefixWord, tailWord_3432725, baseEnd_3432725] using wordTrace_append hprefix tailTrace_3432725
  have hstable : (prefixWord ++ tailWord_3432725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432725).length < 2 ^ (prefixWord ++ tailWord_3432725).sum := by decide
  have hdescent : baseEnd_3432725 < baseStart_3432725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432743 : List Nat := [1, 1, 8, 1, 1, 1, 3, 2, 5]
def baseStart_3432743 : Nat := 118140960795 + 3432743 * 2 ^ 59
def prefixEnd_3432743 : Nat := 4983230072969 + 3 ^ 40 * 3432743 * 2
def baseEnd_3432743 : Nat := 195849680261885345658401

theorem tailTrace_3432743 : CollatzResearch.WordTrace tailWord_3432743 prefixEnd_3432743 195849680261885345658401 := by
  unfold tailWord_3432743
  simp only [CollatzResearch.WordTrace]
  refine ⟨125202423002765851674502883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83468282001843901116335255 125202423002765851674502883)
  ·
    refine ⟨187803634504148777511754325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125202423002765851674502883 187803634504148777511754325)
    ·
      refine ⟨2200823841845493486465871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 187803634504148777511754325 2200823841845493486465871)
      ·
        refine ⟨3301235762768240229698807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200823841845493486465871 3301235762768240229698807)
        ·
          refine ⟨4951853644152360344548211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3301235762768240229698807 4951853644152360344548211)
          ·
            refine ⟨7427780466228540516822317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4951853644152360344548211 7427780466228540516822317)
            ·
              refine ⟨2785417674835702693808369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7427780466228540516822317 2785417674835702693808369)
              ·
                refine ⟨2089063256126777020356277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2785417674835702693808369 2089063256126777020356277)
                ·
                  refine ⟨195849680261885345658401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2089063256126777020356277 195849680261885345658401)
                  ·
                    rfl

theorem cell23_3432743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 5].length) (baseStart_3432743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432743 prefixEnd_3432743 := by exact prefixLift 3432743
  have htrace : WordTrace (prefixWord ++ tailWord_3432743) baseStart_3432743 baseEnd_3432743 := by
    simpa [prefixWord, tailWord_3432743, baseEnd_3432743] using wordTrace_append hprefix tailTrace_3432743
  have hstable : (prefixWord ++ tailWord_3432743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432743).length < 2 ^ (prefixWord ++ tailWord_3432743).sum := by decide
  have hdescent : baseEnd_3432743 < baseStart_3432743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432748 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 8]
def baseStart_3432748 : Nat := 118140960795 + 3432748 * 2 ^ 59
def prefixEnd_3432748 : Nat := 4983230072969 + 3 ^ 40 * 3432748 * 2
def baseEnd_3432748 : Nat := 195849965528915621262565

theorem tailTrace_3432748 : CollatzResearch.WordTrace tailWord_3432748 prefixEnd_3432748 195849965528915621262565 := by
  unfold tailWord_3432748
  simp only [CollatzResearch.WordTrace]
  refine ⟨62601302683873868764217449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83468403578498491685623265 62601302683873868764217449)
  ·
    refine ⟨46950977012905401573163087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62601302683873868764217449 46950977012905401573163087)
    ·
      refine ⟨70426465519358102359744631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46950977012905401573163087 70426465519358102359744631)
      ·
        refine ⟨105639698279037153539616947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70426465519358102359744631 105639698279037153539616947)
        ·
          refine ⟨158459547418555730309425421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105639698279037153539616947 158459547418555730309425421)
          ·
            refine ⟨59422330281958398866034533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158459547418555730309425421 59422330281958398866034533)
            ·
              refine ⟨11141686927867199787381475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59422330281958398866034533 11141686927867199787381475)
              ·
                refine ⟨16712530391800799681072213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11141686927867199787381475 16712530391800799681072213)
                ·
                  refine ⟨195849965528915621262565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16712530391800799681072213 195849965528915621262565)
                  ·
                    rfl

theorem cell23_3432748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_3432748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432748 prefixEnd_3432748 := by exact prefixLift 3432748
  have htrace : WordTrace (prefixWord ++ tailWord_3432748) baseStart_3432748 baseEnd_3432748 := by
    simpa [prefixWord, tailWord_3432748, baseEnd_3432748] using wordTrace_append hprefix tailTrace_3432748
  have hstable : (prefixWord ++ tailWord_3432748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432748).length < 2 ^ (prefixWord ++ tailWord_3432748).sum := by decide
  have hdescent : baseEnd_3432748 < baseStart_3432748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432809 : List Nat := [1, 2, 1, 1, 1, 3, 5, 4, 1, 1, 3]
def baseStart_3432809 : Nat := 118140960795 + 3432809 * 2 ^ 59
def prefixEnd_3432809 : Nat := 4983230072969 + 3 ^ 40 * 3432809 * 2
def baseEnd_3432809 : Nat := 1762681012080164852700305

theorem tailTrace_3432809 : CollatzResearch.WordTrace tailWord_3432809 prefixEnd_3432809 1762681012080164852700305 := by
  unfold tailWord_3432809
  simp only [CollatzResearch.WordTrace]
  refine ⟨125204830220526744946405481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83469886813684496630936987 125204830220526744946405481)
  ·
    refine ⟨93903622665395058709804111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125204830220526744946405481 93903622665395058709804111)
    ·
      refine ⟨140855433998092588064706167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93903622665395058709804111 140855433998092588064706167)
      ·
        refine ⟨211283150997138882097059251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140855433998092588064706167 211283150997138882097059251)
        ·
          refine ⟨316924726495708323145588877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211283150997138882097059251 316924726495708323145588877)
          ·
            refine ⟨118846772435890621179595829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316924726495708323145588877 118846772435890621179595829)
            ·
              refine ⟨11141884915864745735587109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118846772435890621179595829 11141884915864745735587109)
              ·
                refine ⟨2089103421724639825422583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11141884915864745735587109 2089103421724639825422583)
                ·
                  refine ⟨3133655132586959738133875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089103421724639825422583 3133655132586959738133875)
                  ·
                    refine ⟨4700482698880439607200813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3133655132586959738133875 4700482698880439607200813)
                    ·
                      refine ⟨1762681012080164852700305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4700482698880439607200813 1762681012080164852700305)
                      ·
                        rfl

theorem cell23_3432809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 1, 1, 3].length) (baseStart_3432809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432809 prefixEnd_3432809 := by exact prefixLift 3432809
  have htrace : WordTrace (prefixWord ++ tailWord_3432809) baseStart_3432809 baseEnd_3432809 := by
    simpa [prefixWord, tailWord_3432809, baseEnd_3432809] using wordTrace_append hprefix tailTrace_3432809
  have hstable : (prefixWord ++ tailWord_3432809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432809).length < 2 ^ (prefixWord ++ tailWord_3432809).sum := by decide
  have hdescent : baseEnd_3432809 < baseStart_3432809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432825 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 6, 4]
def baseStart_3432825 : Nat := 118140960795 + 3432825 * 2 ^ 59
def prefixEnd_3432825 : Nat := 4983230072969 + 3 ^ 40 * 3432825 * 2
def baseEnd_3432825 : Nat := 587563075923545596700077

theorem tailTrace_3432825 : CollatzResearch.WordTrace tailWord_3432825 prefixEnd_3432825 587563075923545596700077 := by
  unfold tailWord_3432825
  simp only [CollatzResearch.WordTrace]
  refine ⟨125205413788468779678987929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83470275858979186452658619 125205413788468779678987929)
  ·
    refine ⟨93904060341351584759240947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125205413788468779678987929 93904060341351584759240947)
    ·
      refine ⟨140856090512027377138861421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93904060341351584759240947 140856090512027377138861421)
      ·
        refine ⟨52821033942010266427073033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140856090512027377138861421 52821033942010266427073033)
        ·
          refine ⟨39615775456507699820304775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52821033942010266427073033 39615775456507699820304775)
          ·
            refine ⟨59423663184761549730457163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39615775456507699820304775 59423663184761549730457163)
            ·
              refine ⟨89135494777142324595685745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59423663184761549730457163 89135494777142324595685745)
              ·
                refine ⟨66851621082856743446764309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89135494777142324595685745 66851621082856743446764309)
                ·
                  refine ⟨3133669738258909849067077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66851621082856743446764309 3133669738258909849067077)
                  ·
                    refine ⟨587563075923545596700077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133669738258909849067077 587563075923545596700077)
                    ·
                      rfl

theorem cell23_3432825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 4].length) (baseStart_3432825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432825 prefixEnd_3432825 := by exact prefixLift 3432825
  have htrace : WordTrace (prefixWord ++ tailWord_3432825) baseStart_3432825 baseEnd_3432825 := by
    simpa [prefixWord, tailWord_3432825, baseEnd_3432825] using wordTrace_append hprefix tailTrace_3432825
  have hstable : (prefixWord ++ tailWord_3432825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432825).length < 2 ^ (prefixWord ++ tailWord_3432825).sum := by decide
  have hdescent : baseEnd_3432825 < baseStart_3432825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432846 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_3432846 : Nat := 118140960795 + 3432846 * 2 ^ 59
def prefixEnd_3432846 : Nat := 4983230072969 + 3 ^ 40 * 3432846 * 2
def baseEnd_3432846 : Nat := 587566670288127069312545

theorem tailTrace_3432846 : CollatzResearch.WordTrace tailWord_3432846 prefixEnd_3432846 587566670288127069312545 := by
  unfold tailWord_3432846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15650772465174087533187799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83470786480928466843668261 15650772465174087533187799)
  ·
    refine ⟨23476158697761131299781699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15650772465174087533187799 23476158697761131299781699)
    ·
      refine ⟨35214238046641696949672549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23476158697761131299781699 35214238046641696949672549)
      ·
        refine ⟨6602669633745318178063603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35214238046641696949672549 6602669633745318178063603)
        ·
          refine ⟨9904004450617977267095405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6602669633745318178063603 9904004450617977267095405)
          ·
            refine ⟨3714001668981741475160777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9904004450617977267095405 3714001668981741475160777)
            ·
              refine ⟨2785501251736306106370583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3714001668981741475160777 2785501251736306106370583)
              ·
                refine ⟨4178251877604459159555875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785501251736306106370583 4178251877604459159555875)
                ·
                  refine ⟨6267377816406688739333813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178251877604459159555875 6267377816406688739333813)
                  ·
                    refine ⟨587566670288127069312545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6267377816406688739333813 587566670288127069312545)
                    ·
                      rfl

theorem cell23_3432846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_3432846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432846 prefixEnd_3432846 := by exact prefixLift 3432846
  have htrace : WordTrace (prefixWord ++ tailWord_3432846) baseStart_3432846 baseEnd_3432846 := by
    simpa [prefixWord, tailWord_3432846, baseEnd_3432846] using wordTrace_append hprefix tailTrace_3432846
  have hstable : (prefixWord ++ tailWord_3432846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432846).length < 2 ^ (prefixWord ++ tailWord_3432846).sum := by decide
  have hdescent : baseEnd_3432846 < baseStart_3432846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432866 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_3432866 : Nat := 118140960795 + 3432866 * 2 ^ 59
def prefixEnd_3432866 : Nat := 4983230072969 + 3 ^ 40 * 3432866 * 2
def baseEnd_3432866 : Nat := 1762710280477471129687543

theorem tailTrace_3432866 : CollatzResearch.WordTrace tailWord_3432866 prefixEnd_3432866 1762710280477471129687543 := by
  unfold tailWord_3432866
  simp only [CollatzResearch.WordTrace]
  refine ⟨31301727295330060920307613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83471272787546829120820301 31301727295330060920307613)
  ·
    refine ⟨11738147735748772845115355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31301727295330060920307613 11738147735748772845115355)
    ·
      refine ⟨17607221603623159267673033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11738147735748772845115355 17607221603623159267673033)
      ·
        refine ⟨13205416202717369450754775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17607221603623159267673033 13205416202717369450754775)
        ·
          refine ⟨19808124304076054176132163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13205416202717369450754775 19808124304076054176132163)
          ·
            refine ⟨29712186456114081264198245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19808124304076054176132163 29712186456114081264198245)
            ·
              refine ⟨5571034960521390237037171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29712186456114081264198245 5571034960521390237037171)
              ·
                refine ⟨8356552440782085355555757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5571034960521390237037171 8356552440782085355555757)
                ·
                  refine ⟨3133707165293282008333409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8356552440782085355555757 3133707165293282008333409)
                  ·
                    refine ⟨2350280373969961506250057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3133707165293282008333409 2350280373969961506250057)
                    ·
                      refine ⟨1762710280477471129687543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350280373969961506250057 1762710280477471129687543)
                      ·
                        rfl

theorem cell23_3432866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_3432866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432866 prefixEnd_3432866 := by exact prefixLift 3432866
  have htrace : WordTrace (prefixWord ++ tailWord_3432866) baseStart_3432866 baseEnd_3432866 := by
    simpa [prefixWord, tailWord_3432866, baseEnd_3432866] using wordTrace_append hprefix tailTrace_3432866
  have hstable : (prefixWord ++ tailWord_3432866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432866).length < 2 ^ (prefixWord ++ tailWord_3432866).sum := by decide
  have hdescent : baseEnd_3432866 < baseStart_3432866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432942 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3432942 : Nat := 118140960795 + 3432942 * 2 ^ 59
def prefixEnd_3432942 : Nat := 4983230072969 + 3 ^ 40 * 3432942 * 2
def baseEnd_3432942 : Nat := 1762749305007212832337193

theorem tailTrace_3432942 : CollatzResearch.WordTrace tailWord_3432942 prefixEnd_3432942 1762749305007212832337193 := by
  unfold tailWord_3432942
  simp only [CollatzResearch.WordTrace]
  refine ⟨15651210141130613582624635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83473120752696605773998053 15651210141130613582624635)
  ·
    refine ⟨23476815211695920373936953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15651210141130613582624635 23476815211695920373936953)
    ·
      refine ⟨17607611408771940280452715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23476815211695920373936953 17607611408771940280452715)
      ·
        refine ⟨26411417113157910420679073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17607611408771940280452715 26411417113157910420679073)
        ·
          refine ⟨19808562834868432815509305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26411417113157910420679073 19808562834868432815509305)
          ·
            refine ⟨14856422126151324611631979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19808562834868432815509305 14856422126151324611631979)
            ·
              refine ⟨22284633189226986917447969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14856422126151324611631979 22284633189226986917447969)
              ·
                refine ⟨16713474891920240188085977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22284633189226986917447969 16713474891920240188085977)
                ·
                  refine ⟨12535106168940180141064483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16713474891920240188085977 12535106168940180141064483)
                  ·
                    refine ⟨18802659253410270211596725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12535106168940180141064483 18802659253410270211596725)
                    ·
                      refine ⟨1762749305007212832337193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18802659253410270211596725 1762749305007212832337193)
                      ·
                        rfl

theorem cell23_3432942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3432942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432942 prefixEnd_3432942 := by exact prefixLift 3432942
  have htrace : WordTrace (prefixWord ++ tailWord_3432942) baseStart_3432942 baseEnd_3432942 := by
    simpa [prefixWord, tailWord_3432942, baseEnd_3432942] using wordTrace_append hprefix tailTrace_3432942
  have hstable : (prefixWord ++ tailWord_3432942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432942).length < 2 ^ (prefixWord ++ tailWord_3432942).sum := by decide
  have hdescent : baseEnd_3432942 < baseStart_3432942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432945 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 9]
def baseStart_3432945 : Nat := 118140960795 + 3432945 * 2 ^ 59
def prefixEnd_3432945 : Nat := 4983230072969 + 3 ^ 40 * 3432945 * 2
def baseEnd_3432945 : Nat := 195861205049908480066631

theorem tailTrace_3432945 : CollatzResearch.WordTrace tailWord_3432945 prefixEnd_3432945 195861205049908480066631 := by
  unfold tailWord_3432945
  simp only [CollatzResearch.WordTrace]
  refine ⟨125209790548034040173356289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83473193698689360115570859 125209790548034040173356289)
  ·
    refine ⟨93907342911025530130017217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125209790548034040173356289 93907342911025530130017217)
    ·
      refine ⟨70430507183269147597512913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93907342911025530130017217 70430507183269147597512913)
      ·
        refine ⟨52822880387451860698134685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70430507183269147597512913 52822880387451860698134685)
        ·
          refine ⟨19808580145294447761800507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52822880387451860698134685 19808580145294447761800507)
          ·
            refine ⟨29712870217941671642700761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19808580145294447761800507 29712870217941671642700761)
            ·
              refine ⟨22284652663456253732025571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29712870217941671642700761 22284652663456253732025571)
              ·
                refine ⟨33426978995184380598038357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22284652663456253732025571 33426978995184380598038357)
                ·
                  refine ⟨195861205049908480066631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33426978995184380598038357 195861205049908480066631)
                  ·
                    rfl

theorem cell23_3432945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 9].length) (baseStart_3432945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432945 prefixEnd_3432945 := by exact prefixLift 3432945
  have htrace : WordTrace (prefixWord ++ tailWord_3432945) baseStart_3432945 baseEnd_3432945 := by
    simpa [prefixWord, tailWord_3432945, baseEnd_3432945] using wordTrace_append hprefix tailTrace_3432945
  have hstable : (prefixWord ++ tailWord_3432945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432945).length < 2 ^ (prefixWord ++ tailWord_3432945).sum := by decide
  have hdescent : baseEnd_3432945 < baseStart_3432945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432989 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_3432989 : Nat := 118140960795 + 3432989 * 2 ^ 59
def prefixEnd_3432989 : Nat := 4983230072969 + 3 ^ 40 * 3432989 * 2
def baseEnd_3432989 : Nat := 1762773438597974148449477

theorem tailTrace_3432989 : CollatzResearch.WordTrace tailWord_3432989 prefixEnd_3432989 1762773438597974148449477 := by
  unfold tailWord_3432989
  simp only [CollatzResearch.WordTrace]
  refine ⟨125211395359874635687958021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83474263573249757125305347 125211395359874635687958021)
  ·
    refine ⟨23477136629976494191492129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125211395359874635687958021 23477136629976494191492129)
    ·
      refine ⟨17607852472482370643619097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23477136629976494191492129 17607852472482370643619097)
      ·
        refine ⟨13205889354361777982714323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17607852472482370643619097 13205889354361777982714323)
        ·
          refine ⟨19808834031542666974071485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13205889354361777982714323 19808834031542666974071485)
          ·
            refine ⟨7428312761828500115276807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19808834031542666974071485 7428312761828500115276807)
            ·
              refine ⟨11142469142742750172915211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7428312761828500115276807 11142469142742750172915211)
              ·
                refine ⟨16713703714114125259372817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11142469142742750172915211 16713703714114125259372817)
                ·
                  refine ⟨12535277785585593944529613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16713703714114125259372817 12535277785585593944529613)
                  ·
                    refine ⟨4700729169594597729198605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12535277785585593944529613 4700729169594597729198605)
                    ·
                      refine ⟨1762773438597974148449477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4700729169594597729198605 1762773438597974148449477)
                      ·
                        rfl

theorem cell23_3432989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_3432989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3432989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3432989 prefixEnd_3432989 := by exact prefixLift 3432989
  have htrace : WordTrace (prefixWord ++ tailWord_3432989) baseStart_3432989 baseEnd_3432989 := by
    simpa [prefixWord, tailWord_3432989, baseEnd_3432989] using wordTrace_append hprefix tailTrace_3432989
  have hstable : (prefixWord ++ tailWord_3432989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432989).length < 2 ^ (prefixWord ++ tailWord_3432989).sum := by decide
  have hdescent : baseEnd_3432989 < baseStart_3432989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433029 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 2, 4, 2]
def baseStart_3433029 : Nat := 118140960795 + 3433029 * 2 ^ 59
def prefixEnd_3433029 : Nat := 4983230072969 + 3 ^ 40 * 3433029 * 2
def baseEnd_3433029 : Nat := 1762793977824153991949293

theorem tailTrace_3433029 : CollatzResearch.WordTrace tailWord_3433029 prefixEnd_3433029 1762793977824153991949293 := by
  unfold tailWord_3433029
  simp only [CollatzResearch.WordTrace]
  refine ⟨125212854279729722519414141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83475236186486481679609427 125212854279729722519414141)
  ·
    refine ⟨46954820354898645944780303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125212854279729722519414141 46954820354898645944780303)
    ·
      refine ⟨70432230532347968917170455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46954820354898645944780303 70432230532347968917170455)
      ·
        refine ⟨105648345798521953375755683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70432230532347968917170455 105648345798521953375755683)
        ·
          refine ⟨158472518697782930063633525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105648345798521953375755683 158472518697782930063633525)
          ·
            refine ⟨14856798627917149693465643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158472518697782930063633525 14856798627917149693465643)
            ·
              refine ⟨22285197941875724540198465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14856798627917149693465643 22285197941875724540198465)
              ·
                refine ⟨16713898456406793405148849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22285197941875724540198465 16713898456406793405148849)
                ·
                  refine ⟨12535423842305095053861637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16713898456406793405148849 12535423842305095053861637)
                  ·
                    refine ⟨2350391970432205322599057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12535423842305095053861637 2350391970432205322599057)
                    ·
                      refine ⟨1762793977824153991949293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350391970432205322599057 1762793977824153991949293)
                      ·
                        rfl

theorem cell23_3433029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 4, 2].length) (baseStart_3433029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433029 prefixEnd_3433029 := by exact prefixLift 3433029
  have htrace : WordTrace (prefixWord ++ tailWord_3433029) baseStart_3433029 baseEnd_3433029 := by
    simpa [prefixWord, tailWord_3433029, baseEnd_3433029] using wordTrace_append hprefix tailTrace_3433029
  have hstable : (prefixWord ++ tailWord_3433029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433029).length < 2 ^ (prefixWord ++ tailWord_3433029).sum := by decide
  have hdescent : baseEnd_3433029 < baseStart_3433029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433042 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3433042 : Nat := 118140960795 + 3433042 * 2 ^ 59
def prefixEnd_3433042 : Nat := 4983230072969 + 3 ^ 40 * 3433042 * 2
def baseEnd_3433042 : Nat := 1762800653072662441086733

theorem tailTrace_3433042 : CollatzResearch.WordTrace tailWord_3433042 prefixEnd_3433042 1762800653072662441086733 := by
  unfold tailWord_3433042
  simp only [CollatzResearch.WordTrace]
  refine ⟨31303332107170656434909345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83475552285788417159758253 31303332107170656434909345)
  ·
    refine ⟨23477499080377992326182009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31303332107170656434909345 23477499080377992326182009)
    ·
      refine ⟨17608124310283494244636507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23477499080377992326182009 17608124310283494244636507)
      ·
        refine ⟨26412186465425241366954761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17608124310283494244636507 26412186465425241366954761)
        ·
          refine ⟨19809139849068931025216071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26412186465425241366954761 19809139849068931025216071)
          ·
            refine ⟨29713709773603396537824107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19809139849068931025216071 29713709773603396537824107)
            ·
              refine ⟨44570564660405094806736161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29713709773603396537824107 44570564660405094806736161)
              ·
                refine ⟨33427923495303821105052121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44570564660405094806736161 33427923495303821105052121)
                ·
                  refine ⟨25070942621477865828789091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33427923495303821105052121 25070942621477865828789091)
                  ·
                    refine ⟨37606413932216798743183637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25070942621477865828789091 37606413932216798743183637)
                    ·
                      refine ⟨1762800653072662441086733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37606413932216798743183637 1762800653072662441086733)
                      ·
                        rfl

theorem cell23_3433042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3433042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433042 prefixEnd_3433042 := by exact prefixLift 3433042
  have htrace : WordTrace (prefixWord ++ tailWord_3433042) baseStart_3433042 baseEnd_3433042 := by
    simpa [prefixWord, tailWord_3433042, baseEnd_3433042] using wordTrace_append hprefix tailTrace_3433042
  have hstable : (prefixWord ++ tailWord_3433042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433042).length < 2 ^ (prefixWord ++ tailWord_3433042).sum := by decide
  have hdescent : baseEnd_3433042 < baseStart_3433042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433079 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 5, 1, 3]
def baseStart_3433079 : Nat := 118140960795 + 3433079 * 2 ^ 59
def prefixEnd_3433079 : Nat := 4983230072969 + 3 ^ 40 * 3433079 * 2
def baseEnd_3433079 : Nat := 1762819651856878796324063

theorem tailTrace_3433079 : CollatzResearch.WordTrace tailWord_3433079 prefixEnd_3433079 1762819651856878796324063 := by
  unfold tailWord_3433079
  simp only [CollatzResearch.WordTrace]
  refine ⟨125214677929548581058734291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83476451953032387372489527 125214677929548581058734291)
  ·
    refine ⟨187822016894322871588101437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125214677929548581058734291 187822016894322871588101437)
    ·
      refine ⟨70433256335371076845538039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187822016894322871588101437 70433256335371076845538039)
      ·
        refine ⟨105649884503056615268307059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70433256335371076845538039 105649884503056615268307059)
        ·
          refine ⟨158474826754584922902460589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105649884503056615268307059 158474826754584922902460589)
          ·
            refine ⟨59428060032969346088422721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158474826754584922902460589 59428060032969346088422721)
            ·
              refine ⟨44571045024727009566317041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59428060032969346088422721 44571045024727009566317041)
              ·
                refine ⟨33428283768545257174737781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44571045024727009566317041 33428283768545257174737781)
                ·
                  refine ⟨3133901603301117860131667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33428283768545257174737781 3133901603301117860131667)
                  ·
                    refine ⟨4700852404951676790197501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3133901603301117860131667 4700852404951676790197501)
                    ·
                      refine ⟨1762819651856878796324063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4700852404951676790197501 1762819651856878796324063)
                      ·
                        rfl

theorem cell23_3433079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_3433079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433079 prefixEnd_3433079 := by exact prefixLift 3433079
  have htrace : WordTrace (prefixWord ++ tailWord_3433079) baseStart_3433079 baseEnd_3433079 := by
    simpa [prefixWord, tailWord_3433079, baseEnd_3433079] using wordTrace_append hprefix tailTrace_3433079
  have hstable : (prefixWord ++ tailWord_3433079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433079).length < 2 ^ (prefixWord ++ tailWord_3433079).sum := by decide
  have hdescent : baseEnd_3433079 < baseStart_3433079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433116 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 1, 5]
def baseStart_3433116 : Nat := 118140960795 + 3433116 * 2 ^ 59
def prefixEnd_3433116 : Nat := 4983230072969 + 3 ^ 40 * 3433116 * 2
def baseEnd_3433116 : Nat := 587612883547031717187131

theorem tailTrace_3433116 : CollatzResearch.WordTrace tailWord_3433116 prefixEnd_3433116 587612883547031717187131 := by
  unfold tailWord_3433116
  simp only [CollatzResearch.WordTrace]
  refine ⟨62608013715207268188915601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83477351620276357585220801 62608013715207268188915601)
  ·
    refine ⟨46956010286405451141686701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62608013715207268188915601 46956010286405451141686701)
    ·
      refine ⟨17608503857402044178132513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46956010286405451141686701 17608503857402044178132513)
      ·
        refine ⟨13206377893051533133599385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17608503857402044178132513 13206377893051533133599385)
        ·
          refine ⟨9904783419788649850199539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13206377893051533133599385 9904783419788649850199539)
          ·
            refine ⟨14857175129682974775299309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9904783419788649850199539 14857175129682974775299309)
            ·
              refine ⟨5571440673631115540737241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14857175129682974775299309 5571440673631115540737241)
              ·
                refine ⟨4178580505223336655552931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5571440673631115540737241 4178580505223336655552931)
                ·
                  refine ⟨6267870757835004983329397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178580505223336655552931 6267870757835004983329397)
                  ·
                    refine ⟨587612883547031717187131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6267870757835004983329397 587612883547031717187131)
                    ·
                      rfl

theorem cell23_3433116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_3433116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433116 prefixEnd_3433116 := by exact prefixLift 3433116
  have htrace : WordTrace (prefixWord ++ tailWord_3433116) baseStart_3433116 baseEnd_3433116 := by
    simpa [prefixWord, tailWord_3433116, baseEnd_3433116] using wordTrace_append hprefix tailTrace_3433116
  have hstable : (prefixWord ++ tailWord_3433116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433116).length < 2 ^ (prefixWord ++ tailWord_3433116).sum := by decide
  have hdescent : baseEnd_3433116 < baseStart_3433116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433133 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_3433133 : Nat := 118140960795 + 3433133 * 2 ^ 59
def prefixEnd_3433133 : Nat := 4983230072969 + 3 ^ 40 * 3433133 * 2
def baseEnd_3433133 : Nat := 587615793270740528349605

theorem tailTrace_3433133 : CollatzResearch.WordTrace tailWord_3433133 prefixEnd_3433133 587615793270740528349605 := by
  unfold tailWord_3433133
  simp only [CollatzResearch.WordTrace]
  refine ⟨125216647471352948281200053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83477764980901965520800035 125216647471352948281200053)
  ·
    refine ⟨11739060700439338901362505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125216647471352948281200053 11739060700439338901362505)
    ·
      refine ⟨8804295525329504176021879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11739060700439338901362505 8804295525329504176021879)
      ·
        refine ⟨13206443287994256264032819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8804295525329504176021879 13206443287994256264032819)
        ·
          refine ⟨19809664931991384396049229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13206443287994256264032819 19809664931991384396049229)
          ·
            refine ⟨7428624349496769148518461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19809664931991384396049229 7428624349496769148518461)
            ·
              refine ⟨2785734131061288430694423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7428624349496769148518461 2785734131061288430694423)
              ·
                refine ⟨4178601196591932646041635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785734131061288430694423 4178601196591932646041635)
                ·
                  refine ⟨6267901794887898969062453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178601196591932646041635 6267901794887898969062453)
                  ·
                    refine ⟨587615793270740528349605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6267901794887898969062453 587615793270740528349605)
                    ·
                      rfl

theorem cell23_3433133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_3433133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433133 prefixEnd_3433133 := by exact prefixLift 3433133
  have htrace : WordTrace (prefixWord ++ tailWord_3433133) baseStart_3433133 baseEnd_3433133 := by
    simpa [prefixWord, tailWord_3433133, baseEnd_3433133] using wordTrace_append hprefix tailTrace_3433133
  have hstable : (prefixWord ++ tailWord_3433133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433133).length < 2 ^ (prefixWord ++ tailWord_3433133).sum := by decide
  have hdescent : baseEnd_3433133 < baseStart_3433133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433139 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 5]
def baseStart_3433139 : Nat := 118140960795 + 3433139 * 2 ^ 59
def prefixEnd_3433139 : Nat := 4983230072969 + 3 ^ 40 * 3433139 * 2
def baseEnd_3433139 : Nat := 1762850460696148561573787

theorem tailTrace_3433139 : CollatzResearch.WordTrace tailWord_3433139 prefixEnd_3433139 1762850460696148561573787 := by
  unfold tailWord_3433139
  simp only [CollatzResearch.WordTrace]
  refine ⟨125216866309331211305918471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83477910872887474203945647 125216866309331211305918471)
  ·
    refine ⟨187825299463996816958877707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125216866309331211305918471 187825299463996816958877707)
    ·
      refine ⟨281737949195995225438316561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187825299463996816958877707 281737949195995225438316561)
      ·
        refine ⟨211303461896996419078737421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281737949195995225438316561 211303461896996419078737421)
        ·
          refine ⟨79238798211373657154526533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211303461896996419078737421 79238798211373657154526533)
          ·
            refine ⟨14857274664632560716473725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79238798211373657154526533 14857274664632560716473725)
            ·
              refine ⟨5571477999237210268677647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14857274664632560716473725 5571477999237210268677647)
              ·
                refine ⟨8357216998855815403016471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5571477999237210268677647 8357216998855815403016471)
                ·
                  refine ⟨12535825498283723104524707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8357216998855815403016471 12535825498283723104524707)
                  ·
                    refine ⟨18803738247425584656787061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12535825498283723104524707 18803738247425584656787061)
                    ·
                      refine ⟨1762850460696148561573787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18803738247425584656787061 1762850460696148561573787)
                      ·
                        rfl

theorem cell23_3433139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 5].length) (baseStart_3433139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433139 prefixEnd_3433139 := by exact prefixLift 3433139
  have htrace : WordTrace (prefixWord ++ tailWord_3433139) baseStart_3433139 baseEnd_3433139 := by
    simpa [prefixWord, tailWord_3433139, baseEnd_3433139] using wordTrace_append hprefix tailTrace_3433139
  have hstable : (prefixWord ++ tailWord_3433139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433139).length < 2 ^ (prefixWord ++ tailWord_3433139).sum := by decide
  have hdescent : baseEnd_3433139 < baseStart_3433139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433146 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 2, 4]
def baseStart_3433146 : Nat := 118140960795 + 3433146 * 2 ^ 59
def prefixEnd_3433146 : Nat := 4983230072969 + 3 ^ 40 * 3433146 * 2
def baseEnd_3433146 : Nat := 587618018353576678062085

theorem tailTrace_3433146 : CollatzResearch.WordTrace tailWord_3433146 prefixEnd_3433146 587618018353576678062085 := by
  unfold tailWord_3433146
  simp only [CollatzResearch.WordTrace]
  refine ⟨31304280405076462875355823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83478081080203901000948861 31304280405076462875355823)
  ·
    refine ⟨46956420607614694313033735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31304280405076462875355823 46956420607614694313033735)
    ·
      refine ⟨70434630911422041469550603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46956420607614694313033735 70434630911422041469550603)
      ·
        refine ⟨105651946367133062204325905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70434630911422041469550603 105651946367133062204325905)
        ·
          refine ⟨79238959775349796653244429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105651946367133062204325905 79238959775349796653244429)
          ·
            refine ⟨29714609915756173744966661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79238959775349796653244429 29714609915756173744966661)
            ·
              refine ⟨5571489359204282577181249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29714609915756173744966661 5571489359204282577181249)
              ·
                refine ⟨4178617019403211932885937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5571489359204282577181249 4178617019403211932885937)
                ·
                  refine ⟨3133962764552408949664453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4178617019403211932885937 3133962764552408949664453)
                  ·
                    refine ⟨587618018353576678062085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133962764552408949664453 587618018353576678062085)
                    ·
                      rfl

theorem cell23_3433146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_3433146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433146 prefixEnd_3433146 := by exact prefixLift 3433146
  have htrace : WordTrace (prefixWord ++ tailWord_3433146) baseStart_3433146 baseEnd_3433146 := by
    simpa [prefixWord, tailWord_3433146, baseEnd_3433146] using wordTrace_append hprefix tailTrace_3433146
  have hstable : (prefixWord ++ tailWord_3433146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433146).length < 2 ^ (prefixWord ++ tailWord_3433146).sum := by decide
  have hdescent : baseEnd_3433146 < baseStart_3433146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433156 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_3433156 : Nat := 118140960795 + 3433156 * 2 ^ 59
def prefixEnd_3433156 : Nat := 4983230072969 + 3 ^ 40 * 3433156 * 2
def baseEnd_3433156 : Nat := 1762859189867274995061209

theorem tailTrace_3433156 : CollatzResearch.WordTrace tailWord_3433156 prefixEnd_3433156 1762859189867274995061209 := by
  unfold tailWord_3433156
  simp only [CollatzResearch.WordTrace]
  refine ⟨62608743175134811604643661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83478324233513082139524881 62608743175134811604643661)
  ·
    refine ⟨23478278690675554351741373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62608743175134811604643661 23478278690675554351741373)
    ·
      refine ⟨8804354509003332881903015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23478278690675554351741373 8804354509003332881903015)
      ·
        refine ⟨13206531763504999322854523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8804354509003332881903015 13206531763504999322854523)
        ·
          refine ⟨19809797645257498984281785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13206531763504999322854523 19809797645257498984281785)
          ·
            refine ⟨14857348233943124238211339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19809797645257498984281785 14857348233943124238211339)
            ·
              refine ⟨22286022350914686357317009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14857348233943124238211339 22286022350914686357317009)
              ·
                refine ⟨16714516763186014767987757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22286022350914686357317009 16714516763186014767987757)
                ·
                  refine ⟨6267943786194755537995409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16714516763186014767987757 6267943786194755537995409)
                  ·
                    refine ⟨4700957839646066653496557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6267943786194755537995409 4700957839646066653496557)
                    ·
                      refine ⟨1762859189867274995061209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4700957839646066653496557 1762859189867274995061209)
                      ·
                        rfl

theorem cell23_3433156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_3433156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433156 prefixEnd_3433156 := by exact prefixLift 3433156
  have htrace : WordTrace (prefixWord ++ tailWord_3433156) baseStart_3433156 baseEnd_3433156 := by
    simpa [prefixWord, tailWord_3433156, baseEnd_3433156] using wordTrace_append hprefix tailTrace_3433156
  have hstable : (prefixWord ++ tailWord_3433156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433156).length < 2 ^ (prefixWord ++ tailWord_3433156).sum := by decide
  have hdescent : baseEnd_3433156 < baseStart_3433156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433166 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_3433166 : Nat := 118140960795 + 3433166 * 2 ^ 59
def prefixEnd_3433166 : Nat := 4983230072969 + 3 ^ 40 * 3433166 * 2
def baseEnd_3433166 : Nat := 1762864324673819955936163

theorem tailTrace_3433166 : CollatzResearch.WordTrace tailWord_3433166 prefixEnd_3433166 1762864324673819955936163 := by
  unfold tailWord_3433166
  simp only [CollatzResearch.WordTrace]
  refine ⟨15652231385029174364643919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83478567386822263278100901 15652231385029174364643919)
  ·
    refine ⟨23478347077543761546965879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15652231385029174364643919 23478347077543761546965879)
    ·
      refine ⟨35217520616315642320448819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23478347077543761546965879 35217520616315642320448819)
      ·
        refine ⟨52826280924473463480673229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35217520616315642320448819 52826280924473463480673229)
        ·
          refine ⟨19809855346677548805252461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52826280924473463480673229 19809855346677548805252461)
          ·
            refine ⟨7428695755004080801969673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19809855346677548805252461 7428695755004080801969673)
            ·
              refine ⟨5571521816253060601477255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7428695755004080801969673 5571521816253060601477255)
              ·
                refine ⟨8357282724379590902215883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5571521816253060601477255 8357282724379590902215883)
                ·
                  refine ⟨12535924086569386353323825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8357282724379590902215883 12535924086569386353323825)
                  ·
                    refine ⟨9401943064927039764992869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12535924086569386353323825 9401943064927039764992869)
                    ·
                      refine ⟨1762864324673819955936163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9401943064927039764992869 1762864324673819955936163)
                      ·
                        rfl

theorem cell23_3433166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_3433166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433166 prefixEnd_3433166 := by exact prefixLift 3433166
  have htrace : WordTrace (prefixWord ++ tailWord_3433166) baseStart_3433166 baseEnd_3433166 := by
    simpa [prefixWord, tailWord_3433166, baseEnd_3433166] using wordTrace_append hprefix tailTrace_3433166
  have hstable : (prefixWord ++ tailWord_3433166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433166).length < 2 ^ (prefixWord ++ tailWord_3433166).sum := by decide
  have hdescent : baseEnd_3433166 < baseStart_3433166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433170 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_3433170 : Nat := 118140960795 + 3433170 * 2 ^ 59
def prefixEnd_3433170 : Nat := 4983230072969 + 3 ^ 40 * 3433170 * 2
def baseEnd_3433170 : Nat := 1762866378596437940286145

theorem tailTrace_3433170 : CollatzResearch.WordTrace tailWord_3433170 prefixEnd_3433170 1762866378596437940286145 := by
  unfold tailWord_3433170
  simp only [CollatzResearch.WordTrace]
  refine ⟨31304499243054725900074241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83478664648145935733531309 31304499243054725900074241)
  ·
    refine ⟨23478374432291044425055681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31304499243054725900074241 23478374432291044425055681)
    ·
      refine ⟨17608780824218283318791761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23478374432291044425055681 17608780824218283318791761)
      ·
        refine ⟨13206585618163712489093821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17608780824218283318791761 13206585618163712489093821)
        ·
          refine ⟨4952469606811392183410183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13206585618163712489093821 4952469606811392183410183)
          ·
            refine ⟨7428704410217088275115275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4952469606811392183410183 7428704410217088275115275)
            ·
              refine ⟨11143056615325632412672913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7428704410217088275115275 11143056615325632412672913)
              ·
                refine ⟨8357292461494224309504685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11143056615325632412672913 8357292461494224309504685)
                ·
                  refine ⟨3133984673060334116064257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8357292461494224309504685 3133984673060334116064257)
                  ·
                    refine ⟨2350488504795250587048193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3133984673060334116064257 2350488504795250587048193)
                    ·
                      refine ⟨1762866378596437940286145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350488504795250587048193 1762866378596437940286145)
                      ·
                        rfl

theorem cell23_3433170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_3433170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433170 prefixEnd_3433170 := by exact prefixLift 3433170
  have htrace : WordTrace (prefixWord ++ tailWord_3433170) baseStart_3433170 baseEnd_3433170 := by
    simpa [prefixWord, tailWord_3433170, baseEnd_3433170] using wordTrace_append hprefix tailTrace_3433170
  have hstable : (prefixWord ++ tailWord_3433170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433170).length < 2 ^ (prefixWord ++ tailWord_3433170).sum := by decide
  have hdescent : baseEnd_3433170 < baseStart_3433170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433179 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 4, 7, 2]
def baseStart_3433179 : Nat := 118140960795 + 3433179 * 2 ^ 59
def prefixEnd_3433179 : Nat := 4983230072969 + 3 ^ 40 * 3433179 * 2
def baseEnd_3433179 : Nat := 1762870999922328405073603

theorem tailTrace_3433179 : CollatzResearch.WordTrace tailWord_3433179 prefixEnd_3433179 1762870999922328405073603 := by
  unfold tailWord_3433179
  simp only [CollatzResearch.WordTrace]
  refine ⟨125218325229186298137374591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83478883486124198758249727 125218325229186298137374591)
  ·
    refine ⟨187827487843779447206061887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125218325229186298137374591 187827487843779447206061887)
    ·
      refine ⟨281741231765669170809092831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187827487843779447206061887 281741231765669170809092831)
      ·
        refine ⟨422611847648503756213639247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281741231765669170809092831 422611847648503756213639247)
        ·
          refine ⟨633917771472755634320458871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422611847648503756213639247 633917771472755634320458871)
          ·
            refine ⟨950876657209133451480688307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633917771472755634320458871 950876657209133451480688307)
            ·
              refine ⟨1426314985813700177221032461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950876657209133451480688307 1426314985813700177221032461)
              ·
                refine ⟨534868119680137566457887173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1426314985813700177221032461 534868119680137566457887173)
                ·
                  refine ⟨100287772440025793710853845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534868119680137566457887173 100287772440025793710853845)
                  ·
                    refine ⟨2350494666563104540098137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 100287772440025793710853845 2350494666563104540098137)
                    ·
                      refine ⟨1762870999922328405073603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350494666563104540098137 1762870999922328405073603)
                      ·
                        rfl

theorem cell23_3433179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 7, 2].length) (baseStart_3433179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433179 prefixEnd_3433179 := by exact prefixLift 3433179
  have htrace : WordTrace (prefixWord ++ tailWord_3433179) baseStart_3433179 baseEnd_3433179 := by
    simpa [prefixWord, tailWord_3433179, baseEnd_3433179] using wordTrace_append hprefix tailTrace_3433179
  have hstable : (prefixWord ++ tailWord_3433179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433179).length < 2 ^ (prefixWord ++ tailWord_3433179).sum := by decide
  have hdescent : baseEnd_3433179 < baseStart_3433179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433187 : List Nat := [1, 1, 1, 7, 1, 2, 2, 3, 1, 2, 2]
def baseStart_3433187 : Nat := 118140960795 + 3433187 * 2 ^ 59
def prefixEnd_3433187 : Nat := 4983230072969 + 3 ^ 40 * 3433187 * 2
def baseEnd_3433187 : Nat := 1762875107767564373773567

theorem tailTrace_3433187 : CollatzResearch.WordTrace tailWord_3433187 prefixEnd_3433187 1762875107767564373773567 := by
  unfold tailWord_3433187
  simp only [CollatzResearch.WordTrace]
  refine ⟨125218617013157315503665815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83479078008771543669110543 125218617013157315503665815)
  ·
    refine ⟨187827925519735973255498723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125218617013157315503665815 187827925519735973255498723)
    ·
      refine ⟨281741888279603959883248085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187827925519735973255498723 281741888279603959883248085)
      ·
        refine ⟨6603325506553217809763627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 281741888279603959883248085 6603325506553217809763627)
        ·
          refine ⟨9904988259829826714645441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6603325506553217809763627 9904988259829826714645441)
          ·
            refine ⟨7428741194872370035984081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9904988259829826714645441 7428741194872370035984081)
            ·
              refine ⟨5571555896154277526988061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7428741194872370035984081 5571555896154277526988061)
              ·
                refine ⟨2089333461057854072620523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5571555896154277526988061 2089333461057854072620523)
                ·
                  refine ⟨3134000191586781108930785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089333461057854072620523 3134000191586781108930785)
                  ·
                    refine ⟨2350500143690085831698089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3134000191586781108930785 2350500143690085831698089)
                    ·
                      refine ⟨1762875107767564373773567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350500143690085831698089 1762875107767564373773567)
                      ·
                        rfl

theorem cell23_3433187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_3433187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433187 prefixEnd_3433187 := by exact prefixLift 3433187
  have htrace : WordTrace (prefixWord ++ tailWord_3433187) baseStart_3433187 baseEnd_3433187 := by
    simpa [prefixWord, tailWord_3433187, baseEnd_3433187] using wordTrace_append hprefix tailTrace_3433187
  have hstable : (prefixWord ++ tailWord_3433187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433187).length < 2 ^ (prefixWord ++ tailWord_3433187).sum := by decide
  have hdescent : baseEnd_3433187 < baseStart_3433187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433204 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3433204 : Nat := 118140960795 + 3433204 * 2 ^ 59
def prefixEnd_3433204 : Nat := 4983230072969 + 3 ^ 40 * 3433204 * 2
def baseEnd_3433204 : Nat := 1762883836938690807260989

theorem tailTrace_3433204 : CollatzResearch.WordTrace tailWord_3433204 prefixEnd_3433204 1762883836938690807260989 := by
  unfold tailWord_3433204
  simp only [CollatzResearch.WordTrace]
  refine ⟨62609618527047863703517333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83479491369397151604689777 62609618527047863703517333)
  ·
    refine ⟨2934825868455368611102375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62609618527047863703517333 2934825868455368611102375)
    ·
      refine ⟨4402238802683052916653563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934825868455368611102375 4402238802683052916653563)
      ·
        refine ⟨6603358204024579374980345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4402238802683052916653563 6603358204024579374980345)
        ·
          refine ⟨4952518653018434531235259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6603358204024579374980345 4952518653018434531235259)
          ·
            refine ⟨7428777979527651796852889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4952518653018434531235259 7428777979527651796852889)
            ·
              refine ⟨5571583484645738847639667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7428777979527651796852889 5571583484645738847639667)
              ·
                refine ⟨8357375226968608271459501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5571583484645738847639667 8357375226968608271459501)
                ·
                  refine ⟨3134015710113228101797313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8357375226968608271459501 3134015710113228101797313)
                  ·
                    refine ⟨2350511782584921076347985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3134015710113228101797313 2350511782584921076347985)
                    ·
                      refine ⟨1762883836938690807260989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350511782584921076347985 1762883836938690807260989)
                      ·
                        rfl

theorem cell23_3433204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3433204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433204 prefixEnd_3433204 := by exact prefixLift 3433204
  have htrace : WordTrace (prefixWord ++ tailWord_3433204) baseStart_3433204 baseEnd_3433204 := by
    simpa [prefixWord, tailWord_3433204, baseEnd_3433204] using wordTrace_append hprefix tailTrace_3433204
  have hstable : (prefixWord ++ tailWord_3433204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433204).length < 2 ^ (prefixWord ++ tailWord_3433204).sum := by decide
  have hdescent : baseEnd_3433204 < baseStart_3433204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433220 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_3433220 : Nat := 118140960795 + 3433220 * 2 ^ 59
def prefixEnd_3433220 : Nat := 4983230072969 + 3 ^ 40 * 3433220 * 2
def baseEnd_3433220 : Nat := 1762892052629162744660915

theorem tailTrace_3433220 : CollatzResearch.WordTrace tailWord_3433220 prefixEnd_3433220 1762892052629162744660915 := by
  unfold tailWord_3433220
  simp only [CollatzResearch.WordTrace]
  refine ⟨62609910311018881069808557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83479880414691841426411409 62609910311018881069808557)
  ·
    refine ⟨23478716366632080401178209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62609910311018881069808557 23478716366632080401178209)
    ·
      refine ⟨17609037274974060300883657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23478716366632080401178209 17609037274974060300883657)
      ·
        refine ⟨13206777956230545225662743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17609037274974060300883657 13206777956230545225662743)
        ·
          refine ⟨19810166934345817838494115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13206777956230545225662743 19810166934345817838494115)
          ·
            refine ⟨29715250401518726757741173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19810166934345817838494115 29715250401518726757741173)
            ·
              refine ⟨2785804725142380633538235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29715250401518726757741173 2785804725142380633538235)
              ·
                refine ⟨4178707087713570950307353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785804725142380633538235 4178707087713570950307353)
                ·
                  refine ⟨3134030315785178212730515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4178707087713570950307353 3134030315785178212730515)
                  ·
                    refine ⟨4701045473677767319095773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3134030315785178212730515 4701045473677767319095773)
                    ·
                      refine ⟨1762892052629162744660915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4701045473677767319095773 1762892052629162744660915)
                      ·
                        rfl

theorem cell23_3433220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_3433220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433220 prefixEnd_3433220 := by exact prefixLift 3433220
  have htrace : WordTrace (prefixWord ++ tailWord_3433220) baseStart_3433220 baseEnd_3433220 := by
    simpa [prefixWord, tailWord_3433220, baseEnd_3433220] using wordTrace_append hprefix tailTrace_3433220
  have hstable : (prefixWord ++ tailWord_3433220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433220).length < 2 ^ (prefixWord ++ tailWord_3433220).sum := by decide
  have hdescent : baseEnd_3433220 < baseStart_3433220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433277 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 2, 2, 2]
def baseStart_3433277 : Nat := 118140960795 + 3433277 * 2 ^ 59
def prefixEnd_3433277 : Nat := 4983230072969 + 3 ^ 40 * 3433277 * 2
def baseEnd_3433277 : Nat := 1762921321026469021648153

theorem tailTrace_3433277 : CollatzResearch.WordTrace tailWord_3433277 prefixEnd_3433277 1762921321026469021648153 := by
  unfold tailWord_3433277
  simp only [CollatzResearch.WordTrace]
  refine ⟨125221899582831260874442085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83481266388554173916294723 125221899582831260874442085)
  ·
    refine ⟨23479106171780861413957891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125221899582831260874442085 23479106171780861413957891)
    ·
      refine ⟨35218659257671292120936837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23479106171780861413957891 35218659257671292120936837)
      ·
        refine ⟨6603498610813367272675657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35218659257671292120936837 6603498610813367272675657)
        ·
          refine ⟨4952623958110025454506743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6603498610813367272675657 4952623958110025454506743)
          ·
            refine ⟨7428935937165038181760115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4952623958110025454506743 7428935937165038181760115)
            ·
              refine ⟨11143403905747557272640173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7428935937165038181760115 11143403905747557272640173)
              ·
                refine ⟨4178776464655333977240065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11143403905747557272640173 4178776464655333977240065)
                ·
                  refine ⟨3134082348491500482930049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4178776464655333977240065 3134082348491500482930049)
                  ·
                    refine ⟨2350561761368625362197537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3134082348491500482930049 2350561761368625362197537)
                    ·
                      refine ⟨1762921321026469021648153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350561761368625362197537 1762921321026469021648153)
                      ·
                        rfl

theorem cell23_3433277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_3433277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433277 prefixEnd_3433277 := by exact prefixLift 3433277
  have htrace : WordTrace (prefixWord ++ tailWord_3433277) baseStart_3433277 baseEnd_3433277 := by
    simpa [prefixWord, tailWord_3433277, baseEnd_3433277] using wordTrace_append hprefix tailTrace_3433277
  have hstable : (prefixWord ++ tailWord_3433277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433277).length < 2 ^ (prefixWord ++ tailWord_3433277).sum := by decide
  have hdescent : baseEnd_3433277 < baseStart_3433277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433299 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 4]
def baseStart_3433299 : Nat := 118140960795 + 3433299 * 2 ^ 59
def prefixEnd_3433299 : Nat := 4983230072969 + 3 ^ 40 * 3433299 * 2
def baseEnd_3433299 : Nat := 1762932617600867935573051

theorem tailTrace_3433299 : CollatzResearch.WordTrace tailWord_3433299 prefixEnd_3433299 1762932617600867935573051 := by
  unfold tailWord_3433299
  simp only [CollatzResearch.WordTrace]
  refine ⟨125222701988751558631742951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83481801325834372421161967 125222701988751558631742951)
  ·
    refine ⟨187834052983127337947614427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125222701988751558631742951 187834052983127337947614427)
    ·
      refine ⟨281751079474691006921421641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187834052983127337947614427 281751079474691006921421641)
      ·
        refine ⟨211313309606018255191066231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281751079474691006921421641 211313309606018255191066231)
        ·
          refine ⟨316969964409027382786599347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211313309606018255191066231 316969964409027382786599347)
          ·
            refine ⟨475454946613541074179899021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316969964409027382786599347 475454946613541074179899021)
            ·
              refine ⟨178295604980077902817462133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475454946613541074179899021 178295604980077902817462133)
              ·
                refine ⟨16715212966882303389137075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178295604980077902817462133 16715212966882303389137075)
                ·
                  refine ⟨25072819450323455083705613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16715212966882303389137075 25072819450323455083705613)
                  ·
                    refine ⟨9402307293871295656389605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25072819450323455083705613 9402307293871295656389605)
                    ·
                      refine ⟨1762932617600867935573051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9402307293871295656389605 1762932617600867935573051)
                      ·
                        rfl

theorem cell23_3433299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_3433299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433299 prefixEnd_3433299 := by exact prefixLift 3433299
  have htrace : WordTrace (prefixWord ++ tailWord_3433299) baseStart_3433299 baseEnd_3433299 := by
    simpa [prefixWord, tailWord_3433299, baseEnd_3433299] using wordTrace_append hprefix tailTrace_3433299
  have hstable : (prefixWord ++ tailWord_3433299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433299).length < 2 ^ (prefixWord ++ tailWord_3433299).sum := by decide
  have hdescent : baseEnd_3433299 < baseStart_3433299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433333 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_3433333 : Nat := 118140960795 + 3433333 * 2 ^ 59
def prefixEnd_3433333 : Nat := 4983230072969 + 3 ^ 40 * 3433333 * 2
def baseEnd_3433333 : Nat := 1762950075943120802547895

theorem tailTrace_3433333 : CollatzResearch.WordTrace tailWord_3433333 prefixEnd_3433333 1762950075943120802547895 := by
  unfold tailWord_3433333
  simp only [CollatzResearch.WordTrace]
  refine ⟨125223942070628382438480653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83482628047085588292320435 125223942070628382438480653)
  ·
    refine ⟨46958978276485643414430245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125223942070628382438480653 46958978276485643414430245)
    ·
      refine ⟨8804808426841058140205671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46958978276485643414430245 8804808426841058140205671)
      ·
        refine ⟨13207212640261587210308507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8804808426841058140205671 13207212640261587210308507)
        ·
          refine ⟨19810818960392380815462761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13207212640261587210308507 19810818960392380815462761)
          ·
            refine ⟨14858114220294285611597071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19810818960392380815462761 14858114220294285611597071)
            ·
              refine ⟨22287171330441428417395607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14858114220294285611597071 22287171330441428417395607)
              ·
                refine ⟨33430756995662142626093411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22287171330441428417395607 33430756995662142626093411)
                ·
                  refine ⟨50146135493493213939140117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33430756995662142626093411 50146135493493213939140117)
                  ·
                    refine ⟨2350600101257494403397193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50146135493493213939140117 2350600101257494403397193)
                    ·
                      refine ⟨1762950075943120802547895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350600101257494403397193 1762950075943120802547895)
                      ·
                        rfl

theorem cell23_3433333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_3433333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433333 prefixEnd_3433333 := by exact prefixLift 3433333
  have htrace : WordTrace (prefixWord ++ tailWord_3433333) baseStart_3433333 baseEnd_3433333 := by
    simpa [prefixWord, tailWord_3433333, baseEnd_3433333] using wordTrace_append hprefix tailTrace_3433333
  have hstable : (prefixWord ++ tailWord_3433333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433333).length < 2 ^ (prefixWord ++ tailWord_3433333).sum := by decide
  have hdescent : baseEnd_3433333 < baseStart_3433333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433353 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 2, 2, 3]
def baseStart_3433353 : Nat := 118140960795 + 3433353 * 2 ^ 59
def prefixEnd_3433353 : Nat := 4983230072969 + 3 ^ 40 * 3433353 * 2
def baseEnd_3433353 : Nat := 1762960345556210724297803

theorem tailTrace_3433353 : CollatzResearch.WordTrace tailWord_3433353 prefixEnd_3433353 1762960345556210724297803 := by
  unfold tailWord_3433353
  simp only [CollatzResearch.WordTrace]
  refine ⟨125224671530555925854208713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83483114353703950569472475 125224671530555925854208713)
  ·
    refine ⟨93918503647916944390656535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125224671530555925854208713 93918503647916944390656535)
    ·
      refine ⟨140877755471875416585984803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93918503647916944390656535 140877755471875416585984803)
      ·
        refine ⟨211316633207813124878977205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140877755471875416585984803 211316633207813124878977205)
        ·
          refine ⟨19810934363232480457404113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211316633207813124878977205 19810934363232480457404113)
          ·
            refine ⟨14858200772424360343053085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19810934363232480457404113 14858200772424360343053085)
            ·
              refine ⟨5571825289659135128644907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14858200772424360343053085 5571825289659135128644907)
              ·
                refine ⟨8357737934488702692967361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5571825289659135128644907 8357737934488702692967361)
                ·
                  refine ⟨6268303450866527019725521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8357737934488702692967361 6268303450866527019725521)
                  ·
                    refine ⟨4701227588149895264794141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6268303450866527019725521 4701227588149895264794141)
                    ·
                      refine ⟨1762960345556210724297803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4701227588149895264794141 1762960345556210724297803)
                      ·
                        rfl

theorem cell23_3433353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2, 3].length) (baseStart_3433353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433353 prefixEnd_3433353 := by exact prefixLift 3433353
  have htrace : WordTrace (prefixWord ++ tailWord_3433353) baseStart_3433353 baseEnd_3433353 := by
    simpa [prefixWord, tailWord_3433353, baseEnd_3433353] using wordTrace_append hprefix tailTrace_3433353
  have hstable : (prefixWord ++ tailWord_3433353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433353).length < 2 ^ (prefixWord ++ tailWord_3433353).sum := by decide
  have hdescent : baseEnd_3433353 < baseStart_3433353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433423 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 4]
def baseStart_3433423 : Nat := 118140960795 + 3433423 * 2 ^ 59
def prefixEnd_3433423 : Nat := 4983230072969 + 3 ^ 40 * 3433423 * 2
def baseEnd_3433423 : Nat := 1762996289202025450422481

theorem tailTrace_3433423 : CollatzResearch.WordTrace tailWord_3433423 prefixEnd_3433423 1762996289202025450422481 := by
  unfold tailWord_3433423
  simp only [CollatzResearch.WordTrace]
  refine ⟨125227224640302327809256923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83484816426868218539504615 125227224640302327809256923)
  ·
    refine ⟨187840836960453491713885385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125227224640302327809256923 187840836960453491713885385)
    ·
      refine ⟨140880627720340118785414039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187840836960453491713885385 140880627720340118785414039)
      ·
        refine ⟨211320941580510178178121059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140880627720340118785414039 211320941580510178178121059)
        ·
          refine ⟨316981412370765267267181589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211320941580510178178121059 316981412370765267267181589)
          ·
            refine ⟨14858503704879621903149137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 316981412370765267267181589 14858503704879621903149137)
            ·
              refine ⟨11143877778659716427361853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14858503704879621903149137 11143877778659716427361853)
              ·
                refine ⟨4178954166997393660260695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11143877778659716427361853 4178954166997393660260695)
                ·
                  refine ⟨6268431250496090490391043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178954166997393660260695 6268431250496090490391043)
                  ·
                    refine ⟨9402646875744135735586565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6268431250496090490391043 9402646875744135735586565)
                    ·
                      refine ⟨1762996289202025450422481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9402646875744135735586565 1762996289202025450422481)
                      ·
                        rfl

theorem cell23_3433423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 1, 4].length) (baseStart_3433423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433423 prefixEnd_3433423 := by exact prefixLift 3433423
  have htrace : WordTrace (prefixWord ++ tailWord_3433423) baseStart_3433423 baseEnd_3433423 := by
    simpa [prefixWord, tailWord_3433423, baseEnd_3433423] using wordTrace_append hprefix tailTrace_3433423
  have hstable : (prefixWord ++ tailWord_3433423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433423).length < 2 ^ (prefixWord ++ tailWord_3433423).sum := by decide
  have hdescent : baseEnd_3433423 < baseStart_3433423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433433 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 4, 4]
def baseStart_3433433 : Nat := 118140960795 + 3433433 * 2 ^ 59
def prefixEnd_3433433 : Nat := 4983230072969 + 3 ^ 40 * 3433433 * 2
def baseEnd_3433433 : Nat := 587667141336190137099145

theorem tailTrace_3433433 : CollatzResearch.WordTrace tailWord_3433433 prefixEnd_3433433 587667141336190137099145 := by
  unfold tailWord_3433433
  simp only [CollatzResearch.WordTrace]
  refine ⟨125227589370266099517120953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83485059580177399678080635 125227589370266099517120953)
  ·
    refine ⟨93920692027699574637840715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125227589370266099517120953 93920692027699574637840715)
    ·
      refine ⟨140881038041549361956761073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93920692027699574637840715 140881038041549361956761073)
      ·
        refine ⟨105660778531162021467570805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140881038041549361956761073 105660778531162021467570805)
        ·
          refine ⟨9905697987296439512584763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105660778531162021467570805 9905697987296439512584763)
          ·
            refine ⟨14858546980944659268877145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9905697987296439512584763 14858546980944659268877145)
            ·
              refine ⟨11143910235708494451657859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14858546980944659268877145 11143910235708494451657859)
              ·
                refine ⟨16715865353562741677486789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11143910235708494451657859 16715865353562741677486789)
                ·
                  refine ⟨3134224753793014064528773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16715865353562741677486789 3134224753793014064528773)
                  ·
                    refine ⟨587667141336190137099145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3134224753793014064528773 587667141336190137099145)
                    ·
                      rfl

theorem cell23_3433433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 4].length) (baseStart_3433433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433433 prefixEnd_3433433 := by exact prefixLift 3433433
  have htrace : WordTrace (prefixWord ++ tailWord_3433433) baseStart_3433433 baseEnd_3433433 := by
    simpa [prefixWord, tailWord_3433433, baseEnd_3433433] using wordTrace_append hprefix tailTrace_3433433
  have hstable : (prefixWord ++ tailWord_3433433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433433).length < 2 ^ (prefixWord ++ tailWord_3433433).sum := by decide
  have hdescent : baseEnd_3433433 < baseStart_3433433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433434 : List Nat := [3, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3]
def baseStart_3433434 : Nat := 118140960795 + 3433434 * 2 ^ 59
def prefixEnd_3433434 : Nat := 4983230072969 + 3 ^ 40 * 3433434 * 2
def baseEnd_3433434 : Nat := 1763001937489224907384931

theorem tailTrace_3433434 : CollatzResearch.WordTrace tailWord_3433434 prefixEnd_3433434 1763001937489224907384931 := by
  unfold tailWord_3433434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31306906460815619171976839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83485083895508317791938237 31306906460815619171976839)
  ·
    refine ⟨46960359691223428757965259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31306906460815619171976839 46960359691223428757965259)
    ·
      refine ⟨70440539536835143136947889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46960359691223428757965259 70440539536835143136947889)
      ·
        refine ⟨52830404652626357352710917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70440539536835143136947889 52830404652626357352710917)
        ·
          refine ⟨9905700872367442003633297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52830404652626357352710917 9905700872367442003633297)
          ·
            refine ⟨7429275654275581502724973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9905700872367442003633297 7429275654275581502724973)
            ·
              refine ⟨2785978370353343063521865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7429275654275581502724973 2785978370353343063521865)
              ·
                refine ⟨2089483777765007297641399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2785978370353343063521865 2089483777765007297641399)
                ·
                  refine ⟨3134225666647510946462099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089483777765007297641399 3134225666647510946462099)
                  ·
                    refine ⟨4701338499971266419693149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3134225666647510946462099 4701338499971266419693149)
                    ·
                      refine ⟨1763001937489224907384931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4701338499971266419693149 1763001937489224907384931)
                      ·
                        rfl

theorem cell23_3433434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_3433434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433434 prefixEnd_3433434 := by exact prefixLift 3433434
  have htrace : WordTrace (prefixWord ++ tailWord_3433434) baseStart_3433434 baseEnd_3433434 := by
    simpa [prefixWord, tailWord_3433434, baseEnd_3433434] using wordTrace_append hprefix tailTrace_3433434
  have hstable : (prefixWord ++ tailWord_3433434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433434).length < 2 ^ (prefixWord ++ tailWord_3433434).sum := by decide
  have hdescent : baseEnd_3433434 < baseStart_3433434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433443 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 3]
def baseStart_3433443 : Nat := 118140960795 + 3433443 * 2 ^ 59
def prefixEnd_3433443 : Nat := 4983230072969 + 3 ^ 40 * 3433443 * 2
def baseEnd_3433443 : Nat := 1763006558815115372172389

theorem tailTrace_3433443 : CollatzResearch.WordTrace tailWord_3433443 prefixEnd_3433443 1763006558815115372172389 := by
  unfold tailWord_3433443
  simp only [CollatzResearch.WordTrace]
  refine ⟨125227954100229871224984983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83485302733486580816656655 125227954100229871224984983)
  ·
    refine ⟨187841931150344806837477475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125227954100229871224984983 187841931150344806837477475)
    ·
      refine ⟨281762896725517210256216213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187841931150344806837477475 281762896725517210256216213)
      ·
        refine ⟨13207635784008619230760135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 281762896725517210256216213 13207635784008619230760135)
        ·
          refine ⟨19811453676012928846140203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13207635784008619230760135 19811453676012928846140203)
          ·
            refine ⟨29717180514019393269210305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19811453676012928846140203 29717180514019393269210305)
            ·
              refine ⟨22287885385514544951907729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29717180514019393269210305 22287885385514544951907729)
              ·
                refine ⟨16715914039135908713930797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22287885385514544951907729 16715914039135908713930797)
                ·
                  refine ⟨6268467764675965767724049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16715914039135908713930797 6268467764675965767724049)
                  ·
                    refine ⟨4701350823506974325793037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6268467764675965767724049 4701350823506974325793037)
                    ·
                      refine ⟨1763006558815115372172389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4701350823506974325793037 1763006558815115372172389)
                      ·
                        rfl

theorem cell23_3433443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_3433443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433443 prefixEnd_3433443 := by exact prefixLift 3433443
  have htrace : WordTrace (prefixWord ++ tailWord_3433443) baseStart_3433443 baseEnd_3433443 := by
    simpa [prefixWord, tailWord_3433443, baseEnd_3433443] using wordTrace_append hprefix tailTrace_3433443
  have hstable : (prefixWord ++ tailWord_3433443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433443).length < 2 ^ (prefixWord ++ tailWord_3433443).sum := by decide
  have hdescent : baseEnd_3433443 < baseStart_3433443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433450 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 2, 4]
def baseStart_3433450 : Nat := 118140960795 + 3433450 * 2 ^ 59
def prefixEnd_3433450 : Nat := 4983230072969 + 3 ^ 40 * 3433450 * 2
def baseEnd_3433450 : Nat := 587670051059898948261619

theorem tailTrace_3433450 : CollatzResearch.WordTrace tailWord_3433450 prefixEnd_3433450 587670051059898948261619 := by
  unfold tailWord_3433450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31307052352801127855122451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83485472940803007613659869 31307052352801127855122451)
  ·
    refine ⟨46960578529201691782683677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31307052352801127855122451 46960578529201691782683677)
    ·
      refine ⟨17610216948450634418506379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46960578529201691782683677 17610216948450634418506379)
      ·
        refine ⟨26415325422675951627759569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17610216948450634418506379 26415325422675951627759569)
        ·
          refine ⟨19811494067006963720819677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26415325422675951627759569 19811494067006963720819677)
          ·
            refine ⟨7429310275127611395307379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19811494067006963720819677 7429310275127611395307379)
            ·
              refine ⟨11143965412691417092961069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7429310275127611395307379 11143965412691417092961069)
              ·
                refine ⟨4178987029759281409860401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11143965412691417092961069 4178987029759281409860401)
                ·
                  refine ⟨3134240272319461057395301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4178987029759281409860401 3134240272319461057395301)
                  ·
                    refine ⟨587670051059898948261619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3134240272319461057395301 587670051059898948261619)
                    ·
                      rfl

theorem cell23_3433450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_3433450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433450 prefixEnd_3433450 := by exact prefixLift 3433450
  have htrace : WordTrace (prefixWord ++ tailWord_3433450) baseStart_3433450 baseEnd_3433450 := by
    simpa [prefixWord, tailWord_3433450, baseEnd_3433450] using wordTrace_append hprefix tailTrace_3433450
  have hstable : (prefixWord ++ tailWord_3433450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433450).length < 2 ^ (prefixWord ++ tailWord_3433450).sum := by decide
  have hdescent : baseEnd_3433450 < baseStart_3433450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433473 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_3433473 : Nat := 118140960795 + 3433473 * 2 ^ 59
def prefixEnd_3433473 : Nat := 4983230072969 + 3 ^ 40 * 3433473 * 2
def baseEnd_3433473 : Nat := 1763021963234750254797251

theorem tailTrace_3433473 : CollatzResearch.WordTrace tailWord_3433473 prefixEnd_3433473 1763021963234750254797251 := by
  unfold tailWord_3433473
  simp only [CollatzResearch.WordTrace]
  refine ⟨125229048290121186348577073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83486032193414124232384715 125229048290121186348577073)
  ·
    refine ⟨93921786217590889761432805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125229048290121186348577073 93921786217590889761432805)
    ·
      refine ⟨17610334915798291830268651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93921786217590889761432805 17610334915798291830268651)
      ·
        refine ⟨26415502373697437745402977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17610334915798291830268651 26415502373697437745402977)
        ·
          refine ⟨19811626780273078309052233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26415502373697437745402977 19811626780273078309052233)
          ·
            refine ⟨14858720085204808731789175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19811626780273078309052233 14858720085204808731789175)
            ·
              refine ⟨22288080127807213097683763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14858720085204808731789175 22288080127807213097683763)
              ·
                refine ⟨33432120191710819646525645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22288080127807213097683763 33432120191710819646525645)
                ·
                  refine ⟨12537045071891557367447117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33432120191710819646525645 12537045071891557367447117)
                  ·
                    refine ⟨4701391901959334012792669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12537045071891557367447117 4701391901959334012792669)
                    ·
                      refine ⟨1763021963234750254797251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4701391901959334012792669 1763021963234750254797251)
                      ·
                        rfl

theorem cell23_3433473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_3433473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433473 prefixEnd_3433473 := by exact prefixLift 3433473
  have htrace : WordTrace (prefixWord ++ tailWord_3433473) baseStart_3433473 baseEnd_3433473 := by
    simpa [prefixWord, tailWord_3433473, baseEnd_3433473] using wordTrace_append hprefix tailTrace_3433473
  have hstable : (prefixWord ++ tailWord_3433473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433473).length < 2 ^ (prefixWord ++ tailWord_3433473).sum := by decide
  have hdescent : baseEnd_3433473 < baseStart_3433473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433530 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2]
def baseStart_3433530 : Nat := 118140960795 + 3433530 * 2 ^ 59
def prefixEnd_3433530 : Nat := 4983230072969 + 3 ^ 40 * 3433530 * 2
def baseEnd_3433530 : Nat := 1763051231632056531784489

theorem tailTrace_3433530 : CollatzResearch.WordTrace tailWord_3433530 prefixEnd_3433530 1763051231632056531784489 := by
  unfold tailWord_3433530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31307781812728671270850511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83487418167276456722268029 31307781812728671270850511)
  ·
    refine ⟨46961672719093006906275767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31307781812728671270850511 46961672719093006906275767)
    ·
      refine ⟨70442509078639510359413651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46961672719093006906275767 70442509078639510359413651)
      ·
        refine ⟨105663763617959265539120477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70442509078639510359413651 105663763617959265539120477)
        ·
          refine ⟨39623911356734724577170179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105663763617959265539120477 39623911356734724577170179)
          ·
            refine ⟨59435867035102086865755269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39623911356734724577170179 59435867035102086865755269)
            ·
              refine ⟨11144225069081641287329113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59435867035102086865755269 11144225069081641287329113)
              ·
                refine ⟨8358168801811230965496835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11144225069081641287329113 8358168801811230965496835)
                ·
                  refine ⟨12537253202716846448245253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8358168801811230965496835 12537253202716846448245253)
                  ·
                    refine ⟨2350734975509408709045985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12537253202716846448245253 2350734975509408709045985)
                    ·
                      refine ⟨1763051231632056531784489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350734975509408709045985 1763051231632056531784489)
                      ·
                        rfl

theorem cell23_3433530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2].length) (baseStart_3433530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433530 prefixEnd_3433530 := by exact prefixLift 3433530
  have htrace : WordTrace (prefixWord ++ tailWord_3433530) baseStart_3433530 baseEnd_3433530 := by
    simpa [prefixWord, tailWord_3433530, baseEnd_3433530] using wordTrace_append hprefix tailTrace_3433530
  have hstable : (prefixWord ++ tailWord_3433530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433530).length < 2 ^ (prefixWord ++ tailWord_3433530).sum := by decide
  have hdescent : baseEnd_3433530 < baseStart_3433530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433534 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_3433534 : Nat := 118140960795 + 3433534 * 2 ^ 59
def prefixEnd_3433534 : Nat := 4983230072969 + 3 ^ 40 * 3433534 * 2
def baseEnd_3433534 : Nat := 1763053285554674516134471

theorem tailTrace_3433534 : CollatzResearch.WordTrace tailWord_3433534 prefixEnd_3433534 1763053285554674516134471 := by
  unfold tailWord_3433534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15653909142862524220818457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83487515428600129177698437 15653909142862524220818457)
  ·
    refine ⟨11740431857146893165613843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15653909142862524220818457 11740431857146893165613843)
    ·
      refine ⟨17610647785720339748420765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11740431857146893165613843 17610647785720339748420765)
      ·
        refine ⟨6603992919645127405657787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17610647785720339748420765 6603992919645127405657787)
        ·
          refine ⟨9905989379467691108486681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6603992919645127405657787 9905989379467691108486681)
          ·
            refine ⟨7429492034600768331365011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9905989379467691108486681 7429492034600768331365011)
            ·
              refine ⟨11144238051901152497047517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7429492034600768331365011 11144238051901152497047517)
              ·
                refine ⟨4179089269462932186392819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11144238051901152497047517 4179089269462932186392819)
                ·
                  refine ⟨6268633904194398279589229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4179089269462932186392819 6268633904194398279589229)
                  ·
                    refine ⟨2350737714072899354845961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6268633904194398279589229 2350737714072899354845961)
                    ·
                      refine ⟨1763053285554674516134471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350737714072899354845961 1763053285554674516134471)
                      ·
                        rfl

theorem cell23_3433534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_3433534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433534 prefixEnd_3433534 := by exact prefixLift 3433534
  have htrace : WordTrace (prefixWord ++ tailWord_3433534) baseStart_3433534 baseEnd_3433534 := by
    simpa [prefixWord, tailWord_3433534, baseEnd_3433534] using wordTrace_append hprefix tailTrace_3433534
  have hstable : (prefixWord ++ tailWord_3433534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433534).length < 2 ^ (prefixWord ++ tailWord_3433534).sum := by decide
  have hdescent : baseEnd_3433534 < baseStart_3433534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433536 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 9]
def baseStart_3433536 : Nat := 118140960795 + 3433536 * 2 ^ 59
def prefixEnd_3433536 : Nat := 4983230072969 + 3 ^ 40 * 3433536 * 2
def baseEnd_3433536 : Nat := 195894923612887056478829

theorem tailTrace_3433536 : CollatzResearch.WordTrace tailWord_3433536 prefixEnd_3433536 195894923612887056478829 := by
  unfold tailWord_3433536
  simp only [CollatzResearch.WordTrace]
  refine ⟨62615673044446474054060231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83487564059261965405413641 62615673044446474054060231)
  ·
    refine ⟨93923509566669711081090347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62615673044446474054060231 93923509566669711081090347)
    ·
      refine ⟨140885264350004566621635521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93923509566669711081090347 140885264350004566621635521)
      ·
        refine ⟨105663948262503424966226641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140885264350004566621635521 105663948262503424966226641)
        ·
          refine ⟨79247961196877568724669981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105663948262503424966226641 79247961196877568724669981)
          ·
            refine ⟨29717985448829088271751243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79247961196877568724669981 29717985448829088271751243)
            ·
              refine ⟨44576978173243632407626865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29717985448829088271751243 44576978173243632407626865)
              ·
                refine ⟨33432733629932724305720149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44576978173243632407626865 33432733629932724305720149)
                ·
                  refine ⟨195894923612887056478829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33432733629932724305720149 195894923612887056478829)
                  ·
                    rfl

theorem cell23_3433536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 9].length) (baseStart_3433536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433536 prefixEnd_3433536 := by exact prefixLift 3433536
  have htrace : WordTrace (prefixWord ++ tailWord_3433536) baseStart_3433536 baseEnd_3433536 := by
    simpa [prefixWord, tailWord_3433536, baseEnd_3433536] using wordTrace_append hprefix tailTrace_3433536
  have hstable : (prefixWord ++ tailWord_3433536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433536).length < 2 ^ (prefixWord ++ tailWord_3433536).sum := by decide
  have hdescent : baseEnd_3433536 < baseStart_3433536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433543 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_3433543 : Nat := 118140960795 + 3433543 * 2 ^ 59
def prefixEnd_3433543 : Nat := 4983230072969 + 3 ^ 40 * 3433543 * 2
def baseEnd_3433543 : Nat := 1763057906880564980921929

theorem tailTrace_3433543 : CollatzResearch.WordTrace tailWord_3433543 prefixEnd_3433543 1763057906880564980921929 := by
  unfold tailWord_3433543
  simp only [CollatzResearch.WordTrace]
  refine ⟨125231601399867588303625283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83487734266578392202416855 125231601399867588303625283)
  ·
    refine ⟨187847402099801382455437925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125231601399867588303625283 187847402099801382455437925)
    ·
      refine ⟨35221387893712759210394611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187847402099801382455437925 35221387893712759210394611)
      ·
        refine ⟨52832081840569138815591917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35221387893712759210394611 52832081840569138815591917)
        ·
          refine ⟨19812030690213427055846969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52832081840569138815591917 19812030690213427055846969)
          ·
            refine ⟨14859023017660070291885227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19812030690213427055846969 14859023017660070291885227)
            ·
              refine ⟨22288534526490105437827841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14859023017660070291885227 22288534526490105437827841)
              ·
                refine ⟨16716400894867579078370881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22288534526490105437827841 16716400894867579078370881)
                ·
                  refine ⟨12537300671150684308778161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16716400894867579078370881 12537300671150684308778161)
                  ·
                    refine ⟨9402975503363013231583621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12537300671150684308778161 9402975503363013231583621)
                    ·
                      refine ⟨1763057906880564980921929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9402975503363013231583621 1763057906880564980921929)
                      ·
                        rfl

theorem cell23_3433543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_3433543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433543 prefixEnd_3433543 := by exact prefixLift 3433543
  have htrace : WordTrace (prefixWord ++ tailWord_3433543) baseStart_3433543 baseEnd_3433543 := by
    simpa [prefixWord, tailWord_3433543, baseEnd_3433543] using wordTrace_append hprefix tailTrace_3433543
  have hstable : (prefixWord ++ tailWord_3433543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433543).length < 2 ^ (prefixWord ++ tailWord_3433543).sum := by decide
  have hdescent : baseEnd_3433543 < baseStart_3433543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433558 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_3433558 : Nat := 118140960795 + 3433558 * 2 ^ 59
def prefixEnd_3433558 : Nat := 4983230072969 + 3 ^ 40 * 3433558 * 2
def baseEnd_3433558 : Nat := 1763065609090382422234361

theorem tailTrace_3433558 : CollatzResearch.WordTrace tailWord_3433558 prefixEnd_3433558 1763065609090382422234361 := by
  unfold tailWord_3433558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7827009280925827866588833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83488098996542163910280885 7827009280925827866588833)
  ·
    refine ⟨5870256960694370899941625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7827009280925827866588833 5870256960694370899941625)
    ·
      refine ⟨4402692720520778174956219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5870256960694370899941625 4402692720520778174956219)
      ·
        refine ⟨6604039080781167262434329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4402692720520778174956219 6604039080781167262434329)
        ·
          refine ⟨4953029310585875446825747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6604039080781167262434329 4953029310585875446825747)
          ·
            refine ⟨7429543965878813170238621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953029310585875446825747 7429543965878813170238621)
            ·
              refine ⟨2786078987204554938839483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7429543965878813170238621 2786078987204554938839483)
              ·
                refine ⟨4179118480806832408259225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786078987204554938839483 4179118480806832408259225)
                ·
                  refine ⟨3134338860605124306194419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4179118480806832408259225 3134338860605124306194419)
                  ·
                    refine ⟨4701508290907686459291629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3134338860605124306194419 4701508290907686459291629)
                    ·
                      refine ⟨1763065609090382422234361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4701508290907686459291629 1763065609090382422234361)
                      ·
                        rfl

theorem cell23_3433558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_3433558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433558 prefixEnd_3433558 := by exact prefixLift 3433558
  have htrace : WordTrace (prefixWord ++ tailWord_3433558) baseStart_3433558 baseEnd_3433558 := by
    simpa [prefixWord, tailWord_3433558, baseEnd_3433558] using wordTrace_append hprefix tailTrace_3433558
  have hstable : (prefixWord ++ tailWord_3433558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433558).length < 2 ^ (prefixWord ++ tailWord_3433558).sum := by decide
  have hdescent : baseEnd_3433558 < baseStart_3433558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433570 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 7]
def baseStart_3433570 : Nat := 118140960795 + 3433570 * 2 ^ 59
def prefixEnd_3433570 : Nat := 4983230072969 + 3 ^ 40 * 3433570 * 2
def baseEnd_3433570 : Nat := 195896863428692930587145

theorem tailTrace_3433570 : CollatzResearch.WordTrace tailWord_3433570 prefixEnd_3433570 195896863428692930587145 := by
  unfold tailWord_3433570
  simp only [CollatzResearch.WordTrace]
  refine ⟨31308146542692442978714541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83488390780513181276572109 31308146542692442978714541)
  ·
    refine ⟨11740554953509666117017953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31308146542692442978714541 11740554953509666117017953)
    ·
      refine ⟨8805416215132249587763465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11740554953509666117017953 8805416215132249587763465)
      ·
        refine ⟨6604062161349187190822599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8805416215132249587763465 6604062161349187190822599)
        ·
          refine ⟨9906093242023780786233899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6604062161349187190822599 9906093242023780786233899)
          ·
            refine ⟨14859139863035671179350849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9906093242023780786233899 14859139863035671179350849)
            ·
              refine ⟨11144354897276753384513137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14859139863035671179350849 11144354897276753384513137)
              ·
                refine ⟨8358266172957565038384853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11144354897276753384513137 8358266172957565038384853)
                ·
                  refine ⟨195896863428692930587145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8358266172957565038384853 195896863428692930587145)
                  ·
                    rfl

theorem cell23_3433570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_3433570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433570 prefixEnd_3433570 := by exact prefixLift 3433570
  have htrace : WordTrace (prefixWord ++ tailWord_3433570) baseStart_3433570 baseEnd_3433570 := by
    simpa [prefixWord, tailWord_3433570, baseEnd_3433570] using wordTrace_append hprefix tailTrace_3433570
  have hstable : (prefixWord ++ tailWord_3433570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433570).length < 2 ^ (prefixWord ++ tailWord_3433570).sum := by decide
  have hdescent : baseEnd_3433570 < baseStart_3433570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433583 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 2, 5]
def baseStart_3433583 : Nat := 118140960795 + 3433583 * 2 ^ 59
def prefixEnd_3433583 : Nat := 4983230072969 + 3 ^ 40 * 3433583 * 2
def baseEnd_3433583 : Nat := 587692815368914941473915

theorem tailTrace_3433583 : CollatzResearch.WordTrace tailWord_3433583 prefixEnd_3433583 587692815368914941473915 := by
  unfold tailWord_3433583
  simp only [CollatzResearch.WordTrace]
  refine ⟨125233060319722675135081403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83488706879815116756720935 125233060319722675135081403)
  ·
    refine ⟨187849590479584012702622105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125233060319722675135081403 187849590479584012702622105)
    ·
      refine ⟨140887192859688009526966579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187849590479584012702622105 140887192859688009526966579)
      ·
        refine ⟨211330789289532014290449869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140887192859688009526966579 211330789289532014290449869)
        ·
          refine ⟨79249045983574505358918701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211330789289532014290449869 79249045983574505358918701)
          ·
            refine ⟨29718392243840439509594513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79249045983574505358918701 29718392243840439509594513)
            ·
              refine ⟨22288794182880329632195885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29718392243840439509594513 22288794182880329632195885)
              ·
                refine ⟨8358297818580123612073457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22288794182880329632195885 8358297818580123612073457)
                ·
                  refine ⟨6268723363935092709055093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8358297818580123612073457 6268723363935092709055093)
                  ·
                    refine ⟨587692815368914941473915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6268723363935092709055093 587692815368914941473915)
                    ·
                      rfl

theorem cell23_3433583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_3433583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433583 prefixEnd_3433583 := by exact prefixLift 3433583
  have htrace : WordTrace (prefixWord ++ tailWord_3433583) baseStart_3433583 baseEnd_3433583 := by
    simpa [prefixWord, tailWord_3433583, baseEnd_3433583] using wordTrace_append hprefix tailTrace_3433583
  have hstable : (prefixWord ++ tailWord_3433583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433583).length < 2 ^ (prefixWord ++ tailWord_3433583).sum := by decide
  have hdescent : baseEnd_3433583 < baseStart_3433583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433660 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 6]
def baseStart_3433660 : Nat := 118140960795 + 3433660 * 2 ^ 59
def prefixEnd_3433660 : Nat := 4983230072969 + 3 ^ 40 * 3433660 * 2
def baseEnd_3433660 : Nat := 195901998235237891462099

theorem tailTrace_3433660 : CollatzResearch.WordTrace tailWord_3433660 prefixEnd_3433660 195901998235237891462099 := by
  unfold tailWord_3433660
  simp only [CollatzResearch.WordTrace]
  refine ⟨62617934370221858642817217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83490579160295811523756289 62617934370221858642817217)
  ·
    refine ⟨46963450777666393982112913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62617934370221858642817217 46963450777666393982112913)
    ·
      refine ⟨35222588083249795486584685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46963450777666393982112913 35222588083249795486584685)
      ·
        refine ⟨13208470531218673307469257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35222588083249795486584685 13208470531218673307469257)
        ·
          refine ⟨9906352898414004980601943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13208470531218673307469257 9906352898414004980601943)
          ·
            refine ⟨14859529347621007470902915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9906352898414004980601943 14859529347621007470902915)
            ·
              refine ⟨22289294021431511206354373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14859529347621007470902915 22289294021431511206354373)
              ·
                refine ⟨4179242629018408351191445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22289294021431511206354373 4179242629018408351191445)
                ·
                  refine ⟨195901998235237891462099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4179242629018408351191445 195901998235237891462099)
                  ·
                    rfl

theorem cell23_3433660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_3433660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433660 prefixEnd_3433660 := by exact prefixLift 3433660
  have htrace : WordTrace (prefixWord ++ tailWord_3433660) baseStart_3433660 baseEnd_3433660 := by
    simpa [prefixWord, tailWord_3433660, baseEnd_3433660] using wordTrace_append hprefix tailTrace_3433660
  have hstable : (prefixWord ++ tailWord_3433660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433660).length < 2 ^ (prefixWord ++ tailWord_3433660).sum := by decide
  have hdescent : baseEnd_3433660 < baseStart_3433660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433664 : List Nat := [2, 1, 1, 2, 6, 1, 1, 4, 1, 4]
def baseStart_3433664 : Nat := 118140960795 + 3433664 * 2 ^ 59
def prefixEnd_3433664 : Nat := 4983230072969 + 3 ^ 40 * 3433664 * 2
def baseEnd_3433664 : Nat := 587706679346586335836291

theorem tailTrace_3433664 : CollatzResearch.WordTrace tailWord_3433664 prefixEnd_3433664 587706679346586335836291 := by
  unfold tailWord_3433664
  simp only [CollatzResearch.WordTrace]
  refine ⟨62618007316214612984390023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83490676421619483979186697 62618007316214612984390023)
  ·
    refine ⟨93927010974321919476585035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62618007316214612984390023 93927010974321919476585035)
    ·
      refine ⟨140890516461482879214877553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93927010974321919476585035 140890516461482879214877553)
      ·
        refine ⟨105667887346112159411158165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140890516461482879214877553 105667887346112159411158165)
        ·
          refine ⟨4953182219349007472398039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105667887346112159411158165 4953182219349007472398039)
          ·
            refine ⟨7429773329023511208597059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953182219349007472398039 7429773329023511208597059)
            ·
              refine ⟨11144659993535266812895589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7429773329023511208597059 11144659993535266812895589)
              ·
                refine ⟨2089623748787862527417923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11144659993535266812895589 2089623748787862527417923)
                ·
                  refine ⟨3134435623181793791126885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089623748787862527417923 3134435623181793791126885)
                  ·
                    refine ⟨587706679346586335836291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3134435623181793791126885 587706679346586335836291)
                    ·
                      rfl

theorem cell23_3433664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 1, 4].length) (baseStart_3433664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433664 prefixEnd_3433664 := by exact prefixLift 3433664
  have htrace : WordTrace (prefixWord ++ tailWord_3433664) baseStart_3433664 baseEnd_3433664 := by
    simpa [prefixWord, tailWord_3433664, baseEnd_3433664] using wordTrace_append hprefix tailTrace_3433664
  have hstable : (prefixWord ++ tailWord_3433664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433664).length < 2 ^ (prefixWord ++ tailWord_3433664).sum := by decide
  have hdescent : baseEnd_3433664 < baseStart_3433664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433690 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 1, 5]
def baseStart_3433690 : Nat := 118140960795 + 3433690 * 2 ^ 59
def prefixEnd_3433690 : Nat := 4983230072969 + 3 ^ 40 * 3433690 * 2
def baseEnd_3433690 : Nat := 587711129512258635261251

theorem tailTrace_3433690 : CollatzResearch.WordTrace tailWord_3433690 prefixEnd_3433690 587711129512258635261251 := by
  unfold tailWord_3433690
  simp only [CollatzResearch.WordTrace]
  refine ⟨31309240732583758102306631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83491308620223354939484349 31309240732583758102306631)
  ·
    refine ⟨46963861098875637153459947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31309240732583758102306631 46963861098875637153459947)
    ·
      refine ⟨70445791648313455730189921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46963861098875637153459947 70445791648313455730189921)
      ·
        refine ⟨52834343736235091797642441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70445791648313455730189921 52834343736235091797642441)
        ·
          refine ⟨39625757802176318848231831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52834343736235091797642441 39625757802176318848231831)
          ·
            refine ⟨59438636703264478272347747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39625757802176318848231831 59438636703264478272347747)
            ·
              refine ⟨89157955054896717408521621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59438636703264478272347747 89157955054896717408521621)
              ·
                refine ⟨4179279143198283628524451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89157955054896717408521621 4179279143198283628524451)
                ·
                  refine ⟨6268918714797425442786677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4179279143198283628524451 6268918714797425442786677)
                  ·
                    refine ⟨587711129512258635261251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6268918714797425442786677 587711129512258635261251)
                    ·
                      rfl

theorem cell23_3433690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_3433690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433690 prefixEnd_3433690 := by exact prefixLift 3433690
  have htrace : WordTrace (prefixWord ++ tailWord_3433690) baseStart_3433690 baseEnd_3433690 := by
    simpa [prefixWord, tailWord_3433690, baseEnd_3433690] using wordTrace_append hprefix tailTrace_3433690
  have hstable : (prefixWord ++ tailWord_3433690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433690).length < 2 ^ (prefixWord ++ tailWord_3433690).sum := by decide
  have hdescent : baseEnd_3433690 < baseStart_3433690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433697 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 1, 5, 2]
def baseStart_3433697 : Nat := 118140960795 + 3433697 * 2 ^ 59
def prefixEnd_3433697 : Nat := 4983230072969 + 3 ^ 40 * 3433697 * 2
def baseEnd_3433697 : Nat := 1763136982901357378396221

theorem tailTrace_3433697 : CollatzResearch.WordTrace tailWord_3433697 prefixEnd_3433697 1763136982901357378396221 := by
  unfold tailWord_3433697
  simp only [CollatzResearch.WordTrace]
  refine ⟨125237218241309672604731345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83491478827539781736487563 125237218241309672604731345)
  ·
    refine ⟨93927913680982254453548509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125237218241309672604731345 93927913680982254453548509)
    ·
      refine ⟨35222967630368345420080691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93927913680982254453548509 35222967630368345420080691)
      ·
        refine ⟨52834451445552518130121037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35222967630368345420080691 52834451445552518130121037)
        ·
          refine ⟨19812919292082194298795389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52834451445552518130121037 19812919292082194298795389)
          ·
            refine ⟨7429844734530822862048271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19812919292082194298795389 7429844734530822862048271)
            ·
              refine ⟨11144767101796234293072407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7429844734530822862048271 11144767101796234293072407)
              ·
                refine ⟨16717150652694351439608611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11144767101796234293072407 16717150652694351439608611)
                ·
                  refine ⟨25075725979041527159412917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16717150652694351439608611 25075725979041527159412917)
                  ·
                    refine ⟨2350849310535143171194961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25075725979041527159412917 2350849310535143171194961)
                    ·
                      refine ⟨1763136982901357378396221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350849310535143171194961 1763136982901357378396221)
                      ·
                        rfl

theorem cell23_3433697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_3433697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433697 prefixEnd_3433697 := by exact prefixLift 3433697
  have htrace : WordTrace (prefixWord ++ tailWord_3433697) baseStart_3433697 baseEnd_3433697 := by
    simpa [prefixWord, tailWord_3433697, baseEnd_3433697] using wordTrace_append hprefix tailTrace_3433697
  have hstable : (prefixWord ++ tailWord_3433697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433697).length < 2 ^ (prefixWord ++ tailWord_3433697).sum := by decide
  have hdescent : baseEnd_3433697 < baseStart_3433697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433707 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 1, 5]
def baseStart_3433707 : Nat := 118140960795 + 3433707 * 2 ^ 59
def prefixEnd_3433707 : Nat := 4983230072969 + 3 ^ 40 * 3433707 * 2
def baseEnd_3433707 : Nat := 587714039235967446423725

theorem tailTrace_3433707 : CollatzResearch.WordTrace tailWord_3433707 prefixEnd_3433707 587714039235967446423725 := by
  unfold tailWord_3433707
  simp only [CollatzResearch.WordTrace]
  refine ⟨125237582971273444312595375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83491721980848962875063583 125237582971273444312595375)
  ·
    refine ⟨187856374456910166468893063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125237582971273444312595375 187856374456910166468893063)
    ·
      refine ⟨281784561685365249703339595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187856374456910166468893063 281784561685365249703339595)
      ·
        refine ⟨422676842528047874555009393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281784561685365249703339595 422676842528047874555009393)
        ·
          refine ⟨317007631896035905916257045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422676842528047874555009393 317007631896035905916257045)
          ·
            refine ⟨14859732745126683089824549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 317007631896035905916257045 14859732745126683089824549)
            ·
              refine ⟨2786199889711253079342103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14859732745126683089824549 2786199889711253079342103)
              ·
                refine ⟨4179299834566879619013155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786199889711253079342103 4179299834566879619013155)
                ·
                  refine ⟨6268949751850319428519733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4179299834566879619013155 6268949751850319428519733)
                  ·
                    refine ⟨587714039235967446423725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6268949751850319428519733 587714039235967446423725)
                    ·
                      rfl

theorem cell23_3433707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 5].length) (baseStart_3433707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433707 prefixEnd_3433707 := by exact prefixLift 3433707
  have htrace : WordTrace (prefixWord ++ tailWord_3433707) baseStart_3433707 baseEnd_3433707 := by
    simpa [prefixWord, tailWord_3433707, baseEnd_3433707] using wordTrace_append hprefix tailTrace_3433707
  have hstable : (prefixWord ++ tailWord_3433707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433707).length < 2 ^ (prefixWord ++ tailWord_3433707).sum := by decide
  have hdescent : baseEnd_3433707 < baseStart_3433707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433723 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 4]
def baseStart_3433723 : Nat := 118140960795 + 3433723 * 2 ^ 59
def prefixEnd_3433723 : Nat := 4983230072969 + 3 ^ 40 * 3433723 * 2
def baseEnd_3433723 : Nat := 1763150333398374276671101

theorem tailTrace_3433723 : CollatzResearch.WordTrace tailWord_3433723 prefixEnd_3433723 1763150333398374276671101 := by
  unfold tailWord_3433723
  simp only [CollatzResearch.WordTrace]
  refine ⟨125238166539215479045177823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83492111026143652696785215 125238166539215479045177823)
  ·
    refine ⟨187857249808823218567766735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125238166539215479045177823 187857249808823218567766735)
    ·
      refine ⟨281785874713234827851650103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187857249808823218567766735 281785874713234827851650103)
      ·
        refine ⟨422678812069852241777475155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281785874713234827851650103 422678812069852241777475155)
        ·
          refine ⟨634018218104778362666212733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422678812069852241777475155 634018218104778362666212733)
          ·
            refine ⟨237756831789291885999829775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 634018218104778362666212733 237756831789291885999829775)
            ·
              refine ⟨356635247683937828999744663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237756831789291885999829775 356635247683937828999744663)
              ·
                refine ⟨534952871525906743499616995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356635247683937828999744663 534952871525906743499616995)
                ·
                  refine ⟨802429307288860115249425493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534952871525906743499616995 802429307288860115249425493)
                  ·
                    refine ⟨9403468444791329475579205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 802429307288860115249425493 9403468444791329475579205)
                    ·
                      refine ⟨1763150333398374276671101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9403468444791329475579205 1763150333398374276671101)
                      ·
                        rfl

theorem cell23_3433723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 4].length) (baseStart_3433723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433723 prefixEnd_3433723 := by exact prefixLift 3433723
  have htrace : WordTrace (prefixWord ++ tailWord_3433723) baseStart_3433723 baseEnd_3433723 := by
    simpa [prefixWord, tailWord_3433723, baseEnd_3433723] using wordTrace_append hprefix tailTrace_3433723
  have hstable : (prefixWord ++ tailWord_3433723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433723).length < 2 ^ (prefixWord ++ tailWord_3433723).sum := by decide
  have hdescent : baseEnd_3433723 < baseStart_3433723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433733 : List Nat := [1, 3, 1, 1, 2, 1, 4, 10]
def baseStart_3433733 : Nat := 118140960795 + 3433733 * 2 ^ 59
def prefixEnd_3433733 : Nat := 4983230072969 + 3 ^ 40 * 3433733 * 2
def baseEnd_3433733 : Nat := 65302054377959971760965

theorem tailTrace_3433733 : CollatzResearch.WordTrace tailWord_3433733 prefixEnd_3433733 65302054377959971760965 := by
  unfold tailWord_3433733
  simp only [CollatzResearch.WordTrace]
  refine ⟨125238531269179250753041853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83492354179452833835361235 125238531269179250753041853)
  ·
    refine ⟨46964449225942219032390695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125238531269179250753041853 46964449225942219032390695)
    ·
      refine ⟨70446673838913328548586043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46964449225942219032390695 70446673838913328548586043)
      ·
        refine ⟨105670010758369992822879065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70446673838913328548586043 105670010758369992822879065)
        ·
          refine ⟨79252508068777494617159299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105670010758369992822879065 79252508068777494617159299)
          ·
            refine ⟨118878762103166241925738949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79252508068777494617159299 118878762103166241925738949)
            ·
              refine ⟨22289767894343670361076053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118878762103166241925738949 22289767894343670361076053)
              ·
                refine ⟨65302054377959971760965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22289767894343670361076053 65302054377959971760965)
                ·
                  rfl

theorem cell23_3433733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 10].length) (baseStart_3433733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433733 prefixEnd_3433733 := by exact prefixLift 3433733
  have htrace : WordTrace (prefixWord ++ tailWord_3433733) baseStart_3433733 baseEnd_3433733 := by
    simpa [prefixWord, tailWord_3433733, baseEnd_3433733] using wordTrace_append hprefix tailTrace_3433733
  have hstable : (prefixWord ++ tailWord_3433733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433733).length < 2 ^ (prefixWord ++ tailWord_3433733).sum := by decide
  have hdescent : baseEnd_3433733 < baseStart_3433733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433740 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_3433740 : Nat := 118140960795 + 3433740 * 2 ^ 59
def prefixEnd_3433740 : Nat := 4983230072969 + 3 ^ 40 * 3433740 * 2
def baseEnd_3433740 : Nat := 1763159062569500710158523

theorem tailTrace_3433740 : CollatzResearch.WordTrace tailWord_3433740 prefixEnd_3433740 1763159062569500710158523 := by
  unfold tailWord_3433740
  simp only [CollatzResearch.WordTrace]
  refine ⟨62619393290076945474273337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83492524386769260632364449 62619393290076945474273337)
  ·
    refine ⟨46964544967557709105705003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62619393290076945474273337 46964544967557709105705003)
    ·
      refine ⟨70446817451336563658557505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46964544967557709105705003 70446817451336563658557505)
      ·
        refine ⟨52835113088502422743918129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70446817451336563658557505 52835113088502422743918129)
        ·
          refine ⟨39626334816376817057938597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52835113088502422743918129 39626334816376817057938597)
          ·
            refine ⟨7429937778070653198363487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39626334816376817057938597 7429937778070653198363487)
            ·
              refine ⟨11144906667105979797545231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7429937778070653198363487 11144906667105979797545231)
              ·
                refine ⟨16717360000658969696317847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11144906667105979797545231 16717360000658969696317847)
                ·
                  refine ⟨25076040000988454544476771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16717360000658969696317847 25076040000988454544476771)
                  ·
                    refine ⟨37614060001482681816715157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25076040000988454544476771 37614060001482681816715157)
                    ·
                      refine ⟨1763159062569500710158523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37614060001482681816715157 1763159062569500710158523)
                      ·
                        rfl

theorem cell23_3433740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_3433740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433740 prefixEnd_3433740 := by exact prefixLift 3433740
  have htrace : WordTrace (prefixWord ++ tailWord_3433740) baseStart_3433740 baseEnd_3433740 := by
    simpa [prefixWord, tailWord_3433740, baseEnd_3433740] using wordTrace_append hprefix tailTrace_3433740
  have hstable : (prefixWord ++ tailWord_3433740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433740).length < 2 ^ (prefixWord ++ tailWord_3433740).sum := by decide
  have hdescent : baseEnd_3433740 < baseStart_3433740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433753 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_3433753 : Nat := 118140960795 + 3433753 * 2 ^ 59
def prefixEnd_3433753 : Nat := 4983230072969 + 3 ^ 40 * 3433753 * 2
def baseEnd_3433753 : Nat := 1763165737818009159295963

theorem tailTrace_3433753 : CollatzResearch.WordTrace tailWord_3433753 prefixEnd_3433753 1763165737818009159295963 := by
  unfold tailWord_3433753
  simp only [CollatzResearch.WordTrace]
  refine ⟨125239260729106794168769913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83492840486071196112513275 125239260729106794168769913)
  ·
    refine ⟨93929445546830095626577435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125239260729106794168769913 93929445546830095626577435)
    ·
      refine ⟨140894168320245143439866153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93929445546830095626577435 140894168320245143439866153)
      ·
        refine ⟨105670626240183857579899615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140894168320245143439866153 105670626240183857579899615)
        ·
          refine ⟨158505939360275786369849423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105670626240183857579899615 158505939360275786369849423)
          ·
            refine ⟨237758909040413679554774135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158505939360275786369849423 237758909040413679554774135)
            ·
              refine ⟨356638363560620519332161203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237758909040413679554774135 356638363560620519332161203)
              ·
                refine ⟨534957545340930778998241805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356638363560620519332161203 534957545340930778998241805)
                ·
                  refine ⟨200609079502849042124340677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534957545340930778998241805 200609079502849042124340677)
                  ·
                    refine ⟨37614202406784195398313877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200609079502849042124340677 37614202406784195398313877)
                    ·
                      refine ⟨1763165737818009159295963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37614202406784195398313877 1763165737818009159295963)
                      ·
                        rfl

theorem cell23_3433753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_3433753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433753 prefixEnd_3433753 := by exact prefixLift 3433753
  have htrace : WordTrace (prefixWord ++ tailWord_3433753) baseStart_3433753 baseEnd_3433753 := by
    simpa [prefixWord, tailWord_3433753, baseEnd_3433753] using wordTrace_append hprefix tailTrace_3433753
  have hstable : (prefixWord ++ tailWord_3433753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433753).length < 2 ^ (prefixWord ++ tailWord_3433753).sum := by decide
  have hdescent : baseEnd_3433753 < baseStart_3433753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433798 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3433798 : Nat := 118140960795 + 3433798 * 2 ^ 59
def prefixEnd_3433798 : Nat := 4983230072969 + 3 ^ 40 * 3433798 * 2
def baseEnd_3433798 : Nat := 1763188844447461483233257

theorem tailTrace_3433798 : CollatzResearch.WordTrace tailWord_3433798 prefixEnd_3433798 1763188844447461483233257 := by
  unfold tailWord_3433798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3913778187935742714192439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83493934675962511236105365 3913778187935742714192439)
  ·
    refine ⟨5870667281903614071288659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3913778187935742714192439 5870667281903614071288659)
    ·
      refine ⟨8806000922855421106932989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5870667281903614071288659 8806000922855421106932989)
      ·
        refine ⟨3302250346070782915099871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8806000922855421106932989 3302250346070782915099871)
        ·
          refine ⟨4953375519106174372649807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302250346070782915099871 4953375519106174372649807)
          ·
            refine ⟨7430063278659261558974711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953375519106174372649807 7430063278659261558974711)
            ·
              refine ⟨11145094917988892338462067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7430063278659261558974711 11145094917988892338462067)
              ·
                refine ⟨16717642376983338507693101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11145094917988892338462067 16717642376983338507693101)
                ·
                  refine ⟨6269115891368751940384913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16717642376983338507693101 6269115891368751940384913)
                  ·
                    refine ⟨4701836918526563955288685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6269115891368751940384913 4701836918526563955288685)
                    ·
                      refine ⟨1763188844447461483233257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4701836918526563955288685 1763188844447461483233257)
                      ·
                        rfl

theorem cell23_3433798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3433798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433798 prefixEnd_3433798 := by exact prefixLift 3433798
  have htrace : WordTrace (prefixWord ++ tailWord_3433798) baseStart_3433798 baseEnd_3433798 := by
    simpa [prefixWord, tailWord_3433798, baseEnd_3433798] using wordTrace_append hprefix tailTrace_3433798
  have hstable : (prefixWord ++ tailWord_3433798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433798).length < 2 ^ (prefixWord ++ tailWord_3433798).sum := by decide
  have hdescent : baseEnd_3433798 < baseStart_3433798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433804 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 3, 3, 2]
def baseStart_3433804 : Nat := 118140960795 + 3433804 * 2 ^ 59
def prefixEnd_3433804 : Nat := 4983230072969 + 3 ^ 40 * 3433804 * 2
def baseEnd_3433804 : Nat := 1763191925331388459758229

theorem tailTrace_3433804 : CollatzResearch.WordTrace tailWord_3433804 prefixEnd_3433804 1763191925331388459758229 := by
  unfold tailWord_3433804
  simp only [CollatzResearch.WordTrace]
  refine ⟨62620560425961014939438233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83494080567948019919250977 62620560425961014939438233)
  ·
    refine ⟨46965420319470761204578675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62620560425961014939438233 46965420319470761204578675)
    ·
      refine ⟨70448130479206141806868013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46965420319470761204578675 70448130479206141806868013)
      ·
        refine ⟨26418048929702303177575505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70448130479206141806868013 26418048929702303177575505)
        ·
          refine ⟨19813536697276727383181629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26418048929702303177575505 19813536697276727383181629)
          ·
            refine ⟨7430076261478772768693111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19813536697276727383181629 7430076261478772768693111)
            ·
              refine ⟨11145114392218159153039667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7430076261478772768693111 11145114392218159153039667)
              ·
                refine ⟨16717671588327238729559501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11145114392218159153039667 16717671588327238729559501)
                ·
                  refine ⟨6269126845622714523584813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16717671588327238729559501 6269126845622714523584813)
                  ·
                    refine ⟨2350922567108517946344305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6269126845622714523584813 2350922567108517946344305)
                    ·
                      refine ⟨1763191925331388459758229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350922567108517946344305 1763191925331388459758229)
                      ·
                        rfl

theorem cell23_3433804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_3433804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433804 prefixEnd_3433804 := by exact prefixLift 3433804
  have htrace : WordTrace (prefixWord ++ tailWord_3433804) baseStart_3433804 baseEnd_3433804 := by
    simpa [prefixWord, tailWord_3433804, baseEnd_3433804] using wordTrace_append hprefix tailTrace_3433804
  have hstable : (prefixWord ++ tailWord_3433804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433804).length < 2 ^ (prefixWord ++ tailWord_3433804).sum := by decide
  have hdescent : baseEnd_3433804 < baseStart_3433804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433810 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_3433810 : Nat := 118140960795 + 3433810 * 2 ^ 59
def prefixEnd_3433810 : Nat := 4983230072969 + 3 ^ 40 * 3433810 * 2
def baseEnd_3433810 : Nat := 587731668738438478761067

theorem tailTrace_3433810 : CollatzResearch.WordTrace tailWord_3433810 prefixEnd_3433810 587731668738438478761067 := by
  unfold tailWord_3433810
  simp only [CollatzResearch.WordTrace]
  refine ⟨31310334922475073225898721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83494226459933528602396589 31310334922475073225898721)
  ·
    refine ⟨23482751191856304919424041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31310334922475073225898721 23482751191856304919424041)
    ·
      refine ⟨17612063393892228689568031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23482751191856304919424041 17612063393892228689568031)
      ·
        refine ⟨26418095090838343034352047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17612063393892228689568031 26418095090838343034352047)
        ·
          refine ⟨39627142636257514551528071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26418095090838343034352047 39627142636257514551528071)
          ·
            refine ⟨59440713954386271827292107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39627142636257514551528071 59440713954386271827292107)
            ·
              refine ⟨89161070931579407740938161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59440713954386271827292107 89161070931579407740938161)
              ·
                refine ⟨66870803198684555805703621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89161070931579407740938161 66870803198684555805703621)
                ·
                  refine ⟨12538275599753354213569429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66870803198684555805703621 12538275599753354213569429)
                  ·
                    refine ⟨587731668738438478761067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12538275599753354213569429 587731668738438478761067)
                    ·
                      rfl

theorem cell23_3433810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_3433810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433810 prefixEnd_3433810 := by exact prefixLift 3433810
  have htrace : WordTrace (prefixWord ++ tailWord_3433810) baseStart_3433810 baseEnd_3433810 := by
    simpa [prefixWord, tailWord_3433810, baseEnd_3433810] using wordTrace_append hprefix tailTrace_3433810
  have hstable : (prefixWord ++ tailWord_3433810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433810).length < 2 ^ (prefixWord ++ tailWord_3433810).sum := by decide
  have hdescent : baseEnd_3433810 < baseStart_3433810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433817 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 3, 4, 2]
def baseStart_3433817 : Nat := 118140960795 + 3433817 * 2 ^ 59
def prefixEnd_3433817 : Nat := 4983230072969 + 3 ^ 40 * 3433817 * 2
def baseEnd_3433817 : Nat := 1763198600579896908895669

theorem tailTrace_3433817 : CollatzResearch.WordTrace tailWord_3433817 prefixEnd_3433817 1763198600579896908895669 := by
  unfold tailWord_3433817
  simp only [CollatzResearch.WordTrace]
  refine ⟨125241595000874933099099705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83494396667249955399399803 125241595000874933099099705)
  ·
    refine ⟨93931196250656199824324779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125241595000874933099099705 93931196250656199824324779)
    ·
      refine ⟨140896794375984299736487169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93931196250656199824324779 140896794375984299736487169)
      ·
        refine ⟨105672595781988224802365377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140896794375984299736487169 105672595781988224802365377)
        ·
          refine ⟨79254446836491168601774033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105672595781988224802365377 79254446836491168601774033)
          ·
            refine ⟨59440835127368376451330525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79254446836491168601774033 59440835127368376451330525)
            ·
              refine ⟨22290313172763141169248947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59440835127368376451330525 22290313172763141169248947)
              ·
                refine ⟨33435469759144711753873421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22290313172763141169248947 33435469759144711753873421)
                ·
                  refine ⟨12538301159679266907702533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33435469759144711753873421 12538301159679266907702533)
                  ·
                    refine ⟨2350931467439862545194225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12538301159679266907702533 2350931467439862545194225)
                    ·
                      refine ⟨1763198600579896908895669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2350931467439862545194225 1763198600579896908895669)
                      ·
                        rfl

theorem cell23_3433817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 4, 2].length) (baseStart_3433817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433817 prefixEnd_3433817 := by exact prefixLift 3433817
  have htrace : WordTrace (prefixWord ++ tailWord_3433817) baseStart_3433817 baseEnd_3433817 := by
    simpa [prefixWord, tailWord_3433817, baseEnd_3433817] using wordTrace_append hprefix tailTrace_3433817
  have hstable : (prefixWord ++ tailWord_3433817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433817).length < 2 ^ (prefixWord ++ tailWord_3433817).sum := by decide
  have hdescent : baseEnd_3433817 < baseStart_3433817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433837 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_3433837 : Nat := 118140960795 + 3433837 * 2 ^ 59
def prefixEnd_3433837 : Nat := 4983230072969 + 3 ^ 40 * 3433837 * 2
def baseEnd_3433837 : Nat := 1763208870192986830645577

theorem tailTrace_3433837 : CollatzResearch.WordTrace tailWord_3433837 prefixEnd_3433837 1763208870192986830645577 := by
  unfold tailWord_3433837
  simp only [CollatzResearch.WordTrace]
  refine ⟨125242324460802476514827765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83494882973868317676551843 125242324460802476514827765)
  ·
    refine ⟨11741467918200232173265103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125242324460802476514827765 11741467918200232173265103)
    ·
      refine ⟨17612201877300348259897655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11741467918200232173265103 17612201877300348259897655)
      ·
        refine ⟨26418302815950522389846483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17612201877300348259897655 26418302815950522389846483)
        ·
          refine ⟨39627454223925783584769725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26418302815950522389846483 39627454223925783584769725)
          ·
            refine ⟨14860295333972168844288647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39627454223925783584769725 14860295333972168844288647)
            ·
              refine ⟨22290443000958253266432971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14860295333972168844288647 22290443000958253266432971)
              ·
                refine ⟨33435664501437379899649457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22290443000958253266432971 33435664501437379899649457)
                ·
                  refine ⟨25076748376078034924737093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33435664501437379899649457 25076748376078034924737093)
                  ·
                    refine ⟨4701890320514631548388205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25076748376078034924737093 4701890320514631548388205)
                    ·
                      refine ⟨1763208870192986830645577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4701890320514631548388205 1763208870192986830645577)
                      ·
                        rfl

theorem cell23_3433837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_3433837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433837 prefixEnd_3433837 := by exact prefixLift 3433837
  have htrace : WordTrace (prefixWord ++ tailWord_3433837) baseStart_3433837 baseEnd_3433837 := by
    simpa [prefixWord, tailWord_3433837, baseEnd_3433837] using wordTrace_append hprefix tailTrace_3433837
  have hstable : (prefixWord ++ tailWord_3433837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433837).length < 2 ^ (prefixWord ++ tailWord_3433837).sum := by decide
  have hdescent : baseEnd_3433837 < baseStart_3433837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433840 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 7]
def baseStart_3433840 : Nat := 118140960795 + 3433840 * 2 ^ 59
def prefixEnd_3433840 : Nat := 4983230072969 + 3 ^ 40 * 3433840 * 2
def baseEnd_3433840 : Nat := 195912267848327813212007

theorem tailTrace_3433840 : CollatzResearch.WordTrace tailWord_3433840 prefixEnd_3433840 195912267848327813212007 := by
  unfold tailWord_3433840
  simp only [CollatzResearch.WordTrace]
  refine ⟨62621216939895804013593487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83494955919861072018124649 62621216939895804013593487)
  ·
    refine ⟨93931825409843706020390231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62621216939895804013593487 93931825409843706020390231)
    ·
      refine ⟨140897738114765559030585347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93931825409843706020390231 140897738114765559030585347)
      ·
        refine ⟨211346607172148338545878021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140897738114765559030585347 211346607172148338545878021)
        ·
          refine ⟨39627488844777813477352129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211346607172148338545878021 39627488844777813477352129)
          ·
            refine ⟨29720616633583360108014097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39627488844777813477352129 29720616633583360108014097)
            ·
              refine ⟨22290462475187520081010573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29720616633583360108014097 22290462475187520081010573)
              ·
                refine ⟨8358923428195320030378965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22290462475187520081010573 8358923428195320030378965)
                ·
                  refine ⟨195912267848327813212007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8358923428195320030378965 195912267848327813212007)
                  ·
                    rfl

theorem cell23_3433840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 7].length) (baseStart_3433840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433840 prefixEnd_3433840 := by exact prefixLift 3433840
  have htrace : WordTrace (prefixWord ++ tailWord_3433840) baseStart_3433840 baseEnd_3433840 := by
    simpa [prefixWord, tailWord_3433840, baseEnd_3433840] using wordTrace_append hprefix tailTrace_3433840
  have hstable : (prefixWord ++ tailWord_3433840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433840).length < 2 ^ (prefixWord ++ tailWord_3433840).sum := by decide
  have hdescent : baseEnd_3433840 < baseStart_3433840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433924 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3433924 : Nat := 118140960795 + 3433924 * 2 ^ 59
def prefixEnd_3433924 : Nat := 4983230072969 + 3 ^ 40 * 3433924 * 2
def baseEnd_3433924 : Nat := 1763253543009927990257677

theorem tailTrace_3433924 : CollatzResearch.WordTrace tailWord_3433924 prefixEnd_3433924 1763253543009927990257677 := by
  unfold tailWord_3433924
  simp only [CollatzResearch.WordTrace]
  refine ⟨62622748805743645186622413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83496998407658193582163217 62622748805743645186622413)
  ·
    refine ⟨23483530802153866944983405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62622748805743645186622413 23483530802153866944983405)
    ·
      refine ⟨8806324050807700104368777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23483530802153866944983405 8806324050807700104368777)
      ·
        refine ⟨6604743038105775078276583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8806324050807700104368777 6604743038105775078276583)
        ·
          refine ⟨9907114557158662617414875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6604743038105775078276583 9907114557158662617414875)
          ·
            refine ⟨14860671835737993926122313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9907114557158662617414875 14860671835737993926122313)
            ·
              refine ⟨11145503876803495444591735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14860671835737993926122313 11145503876803495444591735)
              ·
                refine ⟨16718255815205243166887603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11145503876803495444591735 16718255815205243166887603)
                ·
                  refine ⟨25077383722807864750331405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16718255815205243166887603 25077383722807864750331405)
                  ·
                    refine ⟨9404018896052949281374277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25077383722807864750331405 9404018896052949281374277)
                    ·
                      refine ⟨1763253543009927990257677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9404018896052949281374277 1763253543009927990257677)
                      ·
                        rfl

theorem cell23_3433924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3433924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433924 prefixEnd_3433924 := by exact prefixLift 3433924
  have htrace : WordTrace (prefixWord ++ tailWord_3433924) baseStart_3433924 baseEnd_3433924 := by
    simpa [prefixWord, tailWord_3433924, baseEnd_3433924] using wordTrace_append hprefix tailTrace_3433924
  have hstable : (prefixWord ++ tailWord_3433924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433924).length < 2 ^ (prefixWord ++ tailWord_3433924).sum := by decide
  have hdescent : baseEnd_3433924 < baseStart_3433924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433927 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_3433927 : Nat := 118140960795 + 3433927 * 2 ^ 59
def prefixEnd_3433927 : Nat := 4983230072969 + 3 ^ 40 * 3433927 * 2
def baseEnd_3433927 : Nat := 1763255083451891478520163

theorem tailTrace_3433927 : CollatzResearch.WordTrace tailWord_3433927 prefixEnd_3433927 1763255083451891478520163 := by
  unfold tailWord_3433927
  simp only [CollatzResearch.WordTrace]
  refine ⟨125245607030476421885604035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83497071353650947923736023 125245607030476421885604035)
  ·
    refine ⟨187868410545714632828406053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125245607030476421885604035 187868410545714632828406053)
    ·
      refine ⟨35225326977321493655326135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187868410545714632828406053 35225326977321493655326135)
      ·
        refine ⟨52837990465982240482989203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35225326977321493655326135 52837990465982240482989203)
        ·
          refine ⟨79256985698973360724483805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52837990465982240482989203 79256985698973360724483805)
          ·
            refine ⟨29721369637115010271681427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79256985698973360724483805 29721369637115010271681427)
            ·
              refine ⟨44582054455672515407522141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29721369637115010271681427 44582054455672515407522141)
              ·
                refine ⟨16718270420877193277820803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44582054455672515407522141 16718270420877193277820803)
                ·
                  refine ⟨25077405631315789916731205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16718270420877193277820803 25077405631315789916731205)
                  ·
                    refine ⟨4702013555871710609387101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25077405631315789916731205 4702013555871710609387101)
                    ·
                      refine ⟨1763255083451891478520163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4702013555871710609387101 1763255083451891478520163)
                      ·
                        rfl

theorem cell23_3433927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_3433927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3433927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3433927 prefixEnd_3433927 := by exact prefixLift 3433927
  have htrace : WordTrace (prefixWord ++ tailWord_3433927) baseStart_3433927 baseEnd_3433927 := by
    simpa [prefixWord, tailWord_3433927, baseEnd_3433927] using wordTrace_append hprefix tailTrace_3433927
  have hstable : (prefixWord ++ tailWord_3433927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433927).length < 2 ^ (prefixWord ++ tailWord_3433927).sum := by decide
  have hdescent : baseEnd_3433927 < baseStart_3433927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434045 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_3434045 : Nat := 118140960795 + 3434045 * 2 ^ 59
def prefixEnd_3434045 : Nat := 4983230072969 + 3 ^ 40 * 3434045 * 2
def baseEnd_3434045 : Nat := 587771891389707338948207

theorem tailTrace_3434045 : CollatzResearch.WordTrace tailWord_3434045 prefixEnd_3434045 587771891389707338948207 := by
  unfold tailWord_3434045
  simp only [CollatzResearch.WordTrace]
  refine ⟨125249910844048928038399589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83499940562699285358933059 125249910844048928038399589)
  ·
    refine ⟨23484358283259174007199923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125249910844048928038399589 23484358283259174007199923)
    ·
      refine ⟨35226537424888761010799885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23484358283259174007199923 35226537424888761010799885)
      ·
        refine ⟨13209951534333285379049957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35226537424888761010799885 13209951534333285379049957)
        ·
          refine ⟨2476865912687491008571867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13209951534333285379049957 2476865912687491008571867)
          ·
            refine ⟨3715298869031236512857801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476865912687491008571867 3715298869031236512857801)
            ·
              refine ⟨2786474151773427384643351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3715298869031236512857801 2786474151773427384643351)
              ·
                refine ⟨4179711227660141076965027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786474151773427384643351 4179711227660141076965027)
                ·
                  refine ⟨6269566841490211615447541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4179711227660141076965027 6269566841490211615447541)
                  ·
                    refine ⟨587771891389707338948207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6269566841490211615447541 587771891389707338948207)
                    ·
                      rfl

theorem cell23_3434045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_3434045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434045 prefixEnd_3434045 := by exact prefixLift 3434045
  have htrace : WordTrace (prefixWord ++ tailWord_3434045) baseStart_3434045 baseEnd_3434045 := by
    simpa [prefixWord, tailWord_3434045, baseEnd_3434045] using wordTrace_append hprefix tailTrace_3434045
  have hstable : (prefixWord ++ tailWord_3434045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434045).length < 2 ^ (prefixWord ++ tailWord_3434045).sum := by decide
  have hdescent : baseEnd_3434045 < baseStart_3434045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434097 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 1, 8]
def baseStart_3434097 : Nat := 118140960795 + 3434097 * 2 ^ 59
def prefixEnd_3434097 : Nat := 4983230072969 + 3 ^ 40 * 3434097 * 2
def baseEnd_3434097 : Nat := 587780791721051937798127

theorem tailTrace_3434097 : CollatzResearch.WordTrace tailWord_3434097 prefixEnd_3434097 587780791721051937798127 := by
  unfold tailWord_3434097
  simp only [CollatzResearch.WordTrace]
  refine ⟨125251807439860540919292545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83501204959907027279528363 125251807439860540919292545)
  ·
    refine ⟨93938855579895405689469409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125251807439860540919292545 93938855579895405689469409)
    ·
      refine ⟨70454141684921554267102057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93938855579895405689469409 70454141684921554267102057)
      ·
        refine ⟨52840606263691165700326543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70454141684921554267102057 52840606263691165700326543)
        ·
          refine ⟨79260909395536748550489815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52840606263691165700326543 79260909395536748550489815)
          ·
            refine ⟨118891364093305122825734723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79260909395536748550489815 118891364093305122825734723)
            ·
              refine ⟨178337046139957684238602085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118891364093305122825734723 178337046139957684238602085)
              ·
                refine ⟨33438196151242065794737891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178337046139957684238602085 33438196151242065794737891)
                ·
                  refine ⟨50157294226863098692106837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33438196151242065794737891 50157294226863098692106837)
                  ·
                    refine ⟨587780791721051937798127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50157294226863098692106837 587780791721051937798127)
                    ·
                      rfl

theorem cell23_3434097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_3434097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434097 prefixEnd_3434097 := by exact prefixLift 3434097
  have htrace : WordTrace (prefixWord ++ tailWord_3434097) baseStart_3434097 baseEnd_3434097 := by
    simpa [prefixWord, tailWord_3434097, baseEnd_3434097] using wordTrace_append hprefix tailTrace_3434097
  have hstable : (prefixWord ++ tailWord_3434097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434097).length < 2 ^ (prefixWord ++ tailWord_3434097).sum := by decide
  have hdescent : baseEnd_3434097 < baseStart_3434097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434124 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 2, 4, 3]
def baseStart_3434124 : Nat := 118140960795 + 3434124 * 2 ^ 59
def prefixEnd_3434124 : Nat := 4983230072969 + 3 ^ 40 * 3434124 * 2
def baseEnd_3434124 : Nat := 1763356239140827207756757

theorem tailTrace_3434124 : CollatzResearch.WordTrace tailWord_3434124 prefixEnd_3434124 1763356239140827207756757 := by
  unfold tailWord_3434124
  simp only [CollatzResearch.WordTrace]
  refine ⟨62626396105381362265262713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83501861473841816353683617 62626396105381362265262713)
  ·
    refine ⟨46969797079036021698947035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62626396105381362265262713 46969797079036021698947035)
    ·
      refine ⟨70454695618554032548420553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46969797079036021698947035 70454695618554032548420553)
      ·
        refine ⟨52841021713915524411315415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70454695618554032548420553 52841021713915524411315415)
        ·
          refine ⟨79261532570873286616973123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52841021713915524411315415 79261532570873286616973123)
          ·
            refine ⟨118892298856309929925459685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79261532570873286616973123 118892298856309929925459685)
            ·
              refine ⟨22292306035558111861023691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118892298856309929925459685 22292306035558111861023691)
              ·
                refine ⟨33438459053337167791535537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22292306035558111861023691 33438459053337167791535537)
                ·
                  refine ⟨25078844290002875843651653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33438459053337167791535537 25078844290002875843651653)
                  ·
                    refine ⟨4702283304375539220684685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25078844290002875843651653 4702283304375539220684685)
                    ·
                      refine ⟨1763356239140827207756757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4702283304375539220684685 1763356239140827207756757)
                      ·
                        rfl

theorem cell23_3434124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_3434124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434124 prefixEnd_3434124 := by exact prefixLift 3434124
  have htrace : WordTrace (prefixWord ++ tailWord_3434124) baseStart_3434124 baseEnd_3434124 := by
    simpa [prefixWord, tailWord_3434124, baseEnd_3434124] using wordTrace_append hprefix tailTrace_3434124
  have hstable : (prefixWord ++ tailWord_3434124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434124).length < 2 ^ (prefixWord ++ tailWord_3434124).sum := by decide
  have hdescent : baseEnd_3434124 < baseStart_3434124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434142 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_3434142 : Nat := 118140960795 + 3434142 * 2 ^ 59
def prefixEnd_3434142 : Nat := 4983230072969 + 3 ^ 40 * 3434142 * 2
def baseEnd_3434142 : Nat := 1763365481792608137331675

theorem tailTrace_3434142 : CollatzResearch.WordTrace tailWord_3434142 prefixEnd_3434142 1763365481792608137331675 := by
  unfold tailWord_3434142
  simp only [CollatzResearch.WordTrace]
  refine ⟨15656681090587189200585085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83502299149798342403120453 15656681090587189200585085)
  ·
    refine ⟨5871255408970195950219407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15656681090587189200585085 5871255408970195950219407)
    ·
      refine ⟨8806883113455293925329111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5871255408970195950219407 8806883113455293925329111)
      ·
        refine ⟨13210324670182940887993667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8806883113455293925329111 13210324670182940887993667)
        ·
          refine ⟨19815487005274411331990501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13210324670182940887993667 19815487005274411331990501)
          ·
            refine ⟨3715403813488952124748219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19815487005274411331990501 3715403813488952124748219)
            ·
              refine ⟨5573105720233428187122329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3715403813488952124748219 5573105720233428187122329)
              ·
                refine ⟨4179829290175071140341747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5573105720233428187122329 4179829290175071140341747)
                ·
                  refine ⟨6269743935262606710512621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4179829290175071140341747 6269743935262606710512621)
                  ·
                    refine ⟨2351153975723477516442233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6269743935262606710512621 2351153975723477516442233)
                    ·
                      refine ⟨1763365481792608137331675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2351153975723477516442233 1763365481792608137331675)
                      ·
                        rfl

theorem cell23_3434142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_3434142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434142 prefixEnd_3434142 := by exact prefixLift 3434142
  have htrace : WordTrace (prefixWord ++ tailWord_3434142) baseStart_3434142 baseEnd_3434142 := by
    simpa [prefixWord, tailWord_3434142, baseEnd_3434142] using wordTrace_append hprefix tailTrace_3434142
  have hstable : (prefixWord ++ tailWord_3434142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434142).length < 2 ^ (prefixWord ++ tailWord_3434142).sum := by decide
  have hdescent : baseEnd_3434142 < baseStart_3434142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434184 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_3434184 : Nat := 118140960795 + 3434184 * 2 ^ 59
def prefixEnd_3434184 : Nat := 4983230072969 + 3 ^ 40 * 3434184 * 2
def baseEnd_3434184 : Nat := 1763387047980096973006481

theorem tailTrace_3434184 : CollatzResearch.WordTrace tailWord_3434184 prefixEnd_3434184 1763387047980096973006481 := by
  unfold tailWord_3434184
  simp only [CollatzResearch.WordTrace]
  refine ⟨62627490295272677388854803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83503320393696903185139737 62627490295272677388854803)
  ·
    refine ⟨93941235442909016083282205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62627490295272677388854803 93941235442909016083282205)
    ·
      refine ⟨35227963291090881031230827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93941235442909016083282205 35227963291090881031230827)
      ·
        refine ⟨52841944936636321546846241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35227963291090881031230827 52841944936636321546846241)
        ·
          refine ⟨39631458702477241160134681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52841944936636321546846241 39631458702477241160134681)
          ·
            refine ⟨29723594026857930870101011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39631458702477241160134681 29723594026857930870101011)
            ·
              refine ⟨44585391040286896305151517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29723594026857930870101011 44585391040286896305151517)
              ·
                refine ⟨16719521640107586114431819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44585391040286896305151517 16719521640107586114431819)
                ·
                  refine ⟨25079282460161379171647729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16719521640107586114431819 25079282460161379171647729)
                  ·
                    refine ⟨18809461845121034378735797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25079282460161379171647729 18809461845121034378735797)
                    ·
                      refine ⟨1763387047980096973006481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18809461845121034378735797 1763387047980096973006481)
                      ·
                        rfl

theorem cell23_3434184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_3434184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434184 prefixEnd_3434184 := by exact prefixLift 3434184
  have htrace : WordTrace (prefixWord ++ tailWord_3434184) baseStart_3434184 baseEnd_3434184 := by
    simpa [prefixWord, tailWord_3434184, baseEnd_3434184] using wordTrace_append hprefix tailTrace_3434184
  have hstable : (prefixWord ++ tailWord_3434184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434184).length < 2 ^ (prefixWord ++ tailWord_3434184).sum := by decide
  have hdescent : baseEnd_3434184 < baseStart_3434184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434188 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3434188 : Nat := 118140960795 + 3434188 * 2 ^ 59
def prefixEnd_3434188 : Nat := 4983230072969 + 3 ^ 40 * 3434188 * 2
def baseEnd_3434188 : Nat := 1763389101902714957356463

theorem tailTrace_3434188 : CollatzResearch.WordTrace tailWord_3434188 prefixEnd_3434188 1763389101902714957356463 := by
  unfold tailWord_3434188
  simp only [CollatzResearch.WordTrace]
  refine ⟨62627563241265431730427609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83503417655020575640570145 62627563241265431730427609)
  ·
    refine ⟨46970672430949073797820707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62627563241265431730427609 46970672430949073797820707)
    ·
      refine ⟨70456008646423610696731061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46970672430949073797820707 70456008646423610696731061)
      ·
        refine ⟨6605250810602213502818537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70456008646423610696731061 6605250810602213502818537)
        ·
          refine ⟨4953938107951660127113903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6605250810602213502818537 4953938107951660127113903)
          ·
            refine ⟨7430907161927490190670855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953938107951660127113903 7430907161927490190670855)
            ·
              refine ⟨11146360742891235286006283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7430907161927490190670855 11146360742891235286006283)
              ·
                refine ⟨16719541114336852929009425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11146360742891235286006283 16719541114336852929009425)
                ·
                  refine ⟨12539655835752639696757069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16719541114336852929009425 12539655835752639696757069)
                  ·
                    refine ⟨4702370938407239886283901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12539655835752639696757069 4702370938407239886283901)
                    ·
                      refine ⟨1763389101902714957356463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4702370938407239886283901 1763389101902714957356463)
                      ·
                        rfl

theorem cell23_3434188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3434188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434188 prefixEnd_3434188 := by exact prefixLift 3434188
  have htrace : WordTrace (prefixWord ++ tailWord_3434188) baseStart_3434188 baseEnd_3434188 := by
    simpa [prefixWord, tailWord_3434188, baseEnd_3434188] using wordTrace_append hprefix tailTrace_3434188
  have hstable : (prefixWord ++ tailWord_3434188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434188).length < 2 ^ (prefixWord ++ tailWord_3434188).sum := by decide
  have hdescent : baseEnd_3434188 < baseStart_3434188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434231 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 3]
def baseStart_3434231 : Nat := 118140960795 + 3434231 * 2 ^ 59
def prefixEnd_3434231 : Nat := 4983230072969 + 3 ^ 40 * 3434231 * 2
def baseEnd_3434231 : Nat := 1763411181570858289118765

theorem tailTrace_3434231 : CollatzResearch.WordTrace tailWord_3434231 prefixEnd_3434231 1763411181570858289118765 := by
  unfold tailWord_3434231
  simp only [CollatzResearch.WordTrace]
  refine ⟨125256694821375081804670547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83504463214250054536447031 125256694821375081804670547)
  ·
    refine ⟨187885042232062622707005821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125256694821375081804670547 187885042232062622707005821)
    ·
      refine ⟨70456890837023483515127183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187885042232062622707005821 70456890837023483515127183)
      ·
        refine ⟨105685336255535225272690775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70456890837023483515127183 105685336255535225272690775)
        ·
          refine ⟨158528004383302837909036163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105685336255535225272690775 158528004383302837909036163)
          ·
            refine ⟨237792006574954256863554245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158528004383302837909036163 237792006574954256863554245)
            ·
              refine ⟨44586001232803923161916421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237792006574954256863554245 44586001232803923161916421)
              ·
                refine ⟨8359875231150735592859329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44586001232803923161916421 8359875231150735592859329)
                ·
                  refine ⟨6269906423363051694644497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8359875231150735592859329 6269906423363051694644497)
                  ·
                    refine ⟨4702429817522288770983373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6269906423363051694644497 4702429817522288770983373)
                    ·
                      refine ⟨1763411181570858289118765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4702429817522288770983373 1763411181570858289118765)
                      ·
                        rfl

theorem cell23_3434231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_3434231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434231 prefixEnd_3434231 := by exact prefixLift 3434231
  have htrace : WordTrace (prefixWord ++ tailWord_3434231) baseStart_3434231 baseEnd_3434231 := by
    simpa [prefixWord, tailWord_3434231, baseEnd_3434231] using wordTrace_append hprefix tailTrace_3434231
  have hstable : (prefixWord ++ tailWord_3434231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434231).length < 2 ^ (prefixWord ++ tailWord_3434231).sum := by decide
  have hdescent : baseEnd_3434231 < baseStart_3434231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434332 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 1, 5]
def baseStart_3434332 : Nat := 118140960795 + 3434332 * 2 ^ 59
def prefixEnd_3434332 : Nat := 4983230072969 + 3 ^ 40 * 3434332 * 2
def baseEnd_3434332 : Nat := 587821014372320797985267

theorem tailTrace_3434332 : CollatzResearch.WordTrace tailWord_3434332 prefixEnd_3434332 587821014372320797985267 := by
  unfold tailWord_3434332
  simp only [CollatzResearch.WordTrace]
  refine ⟨62630189297004588027048625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83506919062672784036064833 62630189297004588027048625)
  ·
    refine ⟨46972641972753441020286469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62630189297004588027048625 46972641972753441020286469)
    ·
      refine ⟨8807370369891270191303713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46972641972753441020286469 8807370369891270191303713)
      ·
        refine ⟨6605527777418452643477785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8807370369891270191303713 6605527777418452643477785)
        ·
          refine ⟨4954145833063839482608339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6605527777418452643477785 4954145833063839482608339)
          ·
            refine ⟨7431218749595759223912509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954145833063839482608339 7431218749595759223912509)
            ·
              refine ⟨2786707031098409708967191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7431218749595759223912509 2786707031098409708967191)
              ·
                refine ⟨4180060546647614563450787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786707031098409708967191 4180060546647614563450787)
                ·
                  refine ⟨6270090819971421845176181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180060546647614563450787 6270090819971421845176181)
                  ·
                    refine ⟨587821014372320797985267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6270090819971421845176181 587821014372320797985267)
                    ·
                      rfl

theorem cell23_3434332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_3434332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434332 prefixEnd_3434332 := by exact prefixLift 3434332
  have htrace : WordTrace (prefixWord ++ tailWord_3434332) baseStart_3434332 baseEnd_3434332 := by
    simpa [prefixWord, tailWord_3434332, baseEnd_3434332] using wordTrace_append hprefix tailTrace_3434332
  have hstable : (prefixWord ++ tailWord_3434332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434332).length < 2 ^ (prefixWord ++ tailWord_3434332).sum := by decide
  have hdescent : baseEnd_3434332 < baseStart_3434332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434335 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 1, 1, 4]
def baseStart_3434335 : Nat := 118140960795 + 3434335 * 2 ^ 59
def prefixEnd_3434335 : Nat := 4983230072969 + 3 ^ 40 * 3434335 * 2
def baseEnd_3434335 : Nat := 1763464583558925882218287

theorem tailTrace_3434335 : CollatzResearch.WordTrace tailWord_3434335 prefixEnd_3434335 1763464583558925882218287 := by
  unfold tailWord_3434335
  simp only [CollatzResearch.WordTrace]
  refine ⟨125260488012998307566456459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83506992008665538377637639 125260488012998307566456459)
  ·
    refine ⟨187890732019497461349684689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125260488012998307566456459 187890732019497461349684689)
    ·
      refine ⟨140918049014623096012263517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187890732019497461349684689 140918049014623096012263517)
      ·
        refine ⟨52844268380483661004598819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140918049014623096012263517 52844268380483661004598819)
        ·
          refine ⟨79266402570725491506898229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52844268380483661004598819 79266402570725491506898229)
          ·
            refine ⟨7431225241005514828771709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79266402570725491506898229 7431225241005514828771709)
            ·
              refine ⟨2786709465377068060789391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7431225241005514828771709 2786709465377068060789391)
              ·
                refine ⟨4180064198065602091184087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786709465377068060789391 4180064198065602091184087)
                ·
                  refine ⟨6270096297098403136776131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180064198065602091184087 6270096297098403136776131)
                  ·
                    refine ⟨9405144445647604705164197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6270096297098403136776131 9405144445647604705164197)
                    ·
                      refine ⟨1763464583558925882218287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9405144445647604705164197 1763464583558925882218287)
                      ·
                        rfl

theorem cell23_3434335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_3434335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434335 prefixEnd_3434335 := by exact prefixLift 3434335
  have htrace : WordTrace (prefixWord ++ tailWord_3434335) baseStart_3434335 baseEnd_3434335 := by
    simpa [prefixWord, tailWord_3434335, baseEnd_3434335] using wordTrace_append hprefix tailTrace_3434335
  have hstable : (prefixWord ++ tailWord_3434335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434335).length < 2 ^ (prefixWord ++ tailWord_3434335).sum := by decide
  have hdescent : baseEnd_3434335 < baseStart_3434335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434368 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 3]
def baseStart_3434368 : Nat := 118140960795 + 3434368 * 2 ^ 59
def prefixEnd_3434368 : Nat := 4983230072969 + 3 ^ 40 * 3434368 * 2
def baseEnd_3434368 : Nat := 1763481528420524253105635

theorem tailTrace_3434368 : CollatzResearch.WordTrace tailWord_3434368 prefixEnd_3434368 1763481528420524253105635 := by
  unfold tailWord_3434368
  simp only [CollatzResearch.WordTrace]
  refine ⟨62630845810939377101203879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83507794414585836134938505 62630845810939377101203879)
  ·
    refine ⟨93946268716409065651805819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62630845810939377101203879 93946268716409065651805819)
    ·
      refine ⟨140919403074613598477708729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93946268716409065651805819 140919403074613598477708729)
      ·
        refine ⟨105689552305960198858281547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140919403074613598477708729 105689552305960198858281547)
        ·
          refine ⟨158534328458940298287422321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105689552305960198858281547 158534328458940298287422321)
          ·
            refine ⟨118900746344205223715566741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158534328458940298287422321 118900746344205223715566741)
            ·
              refine ⟨5573472484884619861667191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118900746344205223715566741 5573472484884619861667191)
              ·
                refine ⟨8360208727326929792500787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5573472484884619861667191 8360208727326929792500787)
                ·
                  refine ⟨12540313090990394688751181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8360208727326929792500787 12540313090990394688751181)
                  ·
                    refine ⟨4702617409121398008281693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12540313090990394688751181 4702617409121398008281693)
                    ·
                      refine ⟨1763481528420524253105635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4702617409121398008281693 1763481528420524253105635)
                      ·
                        rfl

theorem cell23_3434368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_3434368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434368 prefixEnd_3434368 := by exact prefixLift 3434368
  have htrace : WordTrace (prefixWord ++ tailWord_3434368) baseStart_3434368 baseEnd_3434368 := by
    simpa [prefixWord, tailWord_3434368, baseEnd_3434368] using wordTrace_append hprefix tailTrace_3434368
  have hstable : (prefixWord ++ tailWord_3434368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434368).length < 2 ^ (prefixWord ++ tailWord_3434368).sum := by decide
  have hdescent : baseEnd_3434368 < baseStart_3434368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434369 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_3434369 : Nat := 118140960795 + 3434369 * 2 ^ 59
def prefixEnd_3434369 : Nat := 4983230072969 + 3 ^ 40 * 3434369 * 2
def baseEnd_3434369 : Nat := 1763482041901178749193131

theorem tailTrace_3434369 : CollatzResearch.WordTrace tailWord_3434369 prefixEnd_3434369 1763482041901178749193131 := by
  unfold tailWord_3434369
  simp only [CollatzResearch.WordTrace]
  refine ⟨125261728094875131373194161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83507818729916754248796107 125261728094875131373194161)
  ·
    refine ⟨93946296071156348529895621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125261728094875131373194161 93946296071156348529895621)
    ·
      refine ⟨17614930513341815349355429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93946296071156348529895621 17614930513341815349355429)
      ·
        refine ⟨3302799471251590378004143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17614930513341815349355429 3302799471251590378004143)
        ·
          refine ⟨4954199206877385567006215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302799471251590378004143 4954199206877385567006215)
          ·
            refine ⟨7431298810316078350509323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954199206877385567006215 7431298810316078350509323)
            ·
              refine ⟨11146948215474117525763985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7431298810316078350509323 11146948215474117525763985)
              ·
                refine ⟨8360211161605588144322989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11146948215474117525763985 8360211161605588144322989)
                ·
                  refine ⟨3135079185602095554121121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8360211161605588144322989 3135079185602095554121121)
                  ·
                    refine ⟨2351309389201571665590841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3135079185602095554121121 2351309389201571665590841)
                    ·
                      refine ⟨1763482041901178749193131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2351309389201571665590841 1763482041901178749193131)
                      ·
                        rfl

theorem cell23_3434369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_3434369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434369 prefixEnd_3434369 := by exact prefixLift 3434369
  have htrace : WordTrace (prefixWord ++ tailWord_3434369) baseStart_3434369 baseEnd_3434369 := by
    simpa [prefixWord, tailWord_3434369, baseEnd_3434369] using wordTrace_append hprefix tailTrace_3434369
  have hstable : (prefixWord ++ tailWord_3434369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434369).length < 2 ^ (prefixWord ++ tailWord_3434369).sum := by decide
  have hdescent : baseEnd_3434369 < baseStart_3434369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434386 : List Nat := [3, 2, 3, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_3434386 : Nat := 118140960795 + 3434386 * 2 ^ 59
def prefixEnd_3434386 : Nat := 4983230072969 + 3 ^ 40 * 3434386 * 2
def baseEnd_3434386 : Nat := 1763490771072305182680553

theorem tailTrace_3434386 : CollatzResearch.WordTrace tailWord_3434386 prefixEnd_3434386 1763490771072305182680553 := by
  unfold tailWord_3434386
  simp only [CollatzResearch.WordTrace]
  refine ⟨31315587033953385819140753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83508232090542362184375341 31315587033953385819140753)
  ·
    refine ⟨23486690275465039364355565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31315587033953385819140753 23486690275465039364355565)
    ·
      refine ⟨8807508853299389761633337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23486690275465039364355565 8807508853299389761633337)
      ·
        refine ⟨6605631639974542321225003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8807508853299389761633337 6605631639974542321225003)
        ·
          refine ⟨9908447459961813481837505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6605631639974542321225003 9908447459961813481837505)
          ·
            refine ⟨7431335594971360111378129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9908447459961813481837505 7431335594971360111378129)
            ·
              refine ⟨5573501696228520083533597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7431335594971360111378129 5573501696228520083533597)
              ·
                refine ⟨2090063136085695031325099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5573501696228520083533597 2090063136085695031325099)
                ·
                  refine ⟨3135094704128542546987649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090063136085695031325099 3135094704128542546987649)
                  ·
                    refine ⟨2351321028096406910240737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3135094704128542546987649 2351321028096406910240737)
                    ·
                      refine ⟨1763490771072305182680553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2351321028096406910240737 1763490771072305182680553)
                      ·
                        rfl

theorem cell23_3434386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_3434386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434386 prefixEnd_3434386 := by exact prefixLift 3434386
  have htrace : WordTrace (prefixWord ++ tailWord_3434386) baseStart_3434386 baseEnd_3434386 := by
    simpa [prefixWord, tailWord_3434386, baseEnd_3434386] using wordTrace_append hprefix tailTrace_3434386
  have hstable : (prefixWord ++ tailWord_3434386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434386).length < 2 ^ (prefixWord ++ tailWord_3434386).sum := by decide
  have hdescent : baseEnd_3434386 < baseStart_3434386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434402 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_3434402 : Nat := 118140960795 + 3434402 * 2 ^ 59
def prefixEnd_3434402 : Nat := 4983230072969 + 3 ^ 40 * 3434402 * 2
def baseEnd_3434402 : Nat := 1763498986762777120080479

theorem tailTrace_3434402 : CollatzResearch.WordTrace tailWord_3434402 prefixEnd_3434402 1763498986762777120080479 := by
  unfold tailWord_3434402
  simp only [CollatzResearch.WordTrace]
  refine ⟨31315732925938894502286365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83508621135837052006096973 31315732925938894502286365)
  ·
    refine ⟨11743399847227085438357387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31315732925938894502286365 11743399847227085438357387)
    ·
      refine ⟨17615099770840628157536081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11743399847227085438357387 17615099770840628157536081)
      ·
        refine ⟨13211324828130471118152061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17615099770840628157536081 13211324828130471118152061)
        ·
          refine ⟨4954246810548926669307023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13211324828130471118152061 4954246810548926669307023)
          ·
            refine ⟨7431370215823390003960535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954246810548926669307023 7431370215823390003960535)
            ·
              refine ⟨11147055323735085005940803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7431370215823390003960535 11147055323735085005940803)
              ·
                refine ⟨16720582985602627508911205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11147055323735085005940803 16720582985602627508911205)
                ·
                  refine ⟨3135109309800492657920851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16720582985602627508911205 3135109309800492657920851)
                  ·
                    refine ⟨4702663964700738986881277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3135109309800492657920851 4702663964700738986881277)
                    ·
                      refine ⟨1763498986762777120080479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4702663964700738986881277 1763498986762777120080479)
                      ·
                        rfl

theorem cell23_3434402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_3434402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434402 prefixEnd_3434402 := by exact prefixLift 3434402
  have htrace : WordTrace (prefixWord ++ tailWord_3434402) baseStart_3434402 baseEnd_3434402 := by
    simpa [prefixWord, tailWord_3434402, baseEnd_3434402] using wordTrace_append hprefix tailTrace_3434402
  have hstable : (prefixWord ++ tailWord_3434402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434402).length < 2 ^ (prefixWord ++ tailWord_3434402).sum := by decide
  have hdescent : baseEnd_3434402 < baseStart_3434402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434431 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 7]
def baseStart_3434431 : Nat := 118140960795 + 3434431 * 2 ^ 59
def prefixEnd_3434431 : Nat := 4983230072969 + 3 ^ 40 * 3434431 * 2
def baseEnd_3434431 : Nat := 195945986411306389624205

theorem tailTrace_3434431 : CollatzResearch.WordTrace tailWord_3434431 prefixEnd_3434431 195945986411306389624205 := by
  unfold tailWord_3434431
  simp only [CollatzResearch.WordTrace]
  refine ⟨125263989420650515961951147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83509326280433677307967431 125263989420650515961951147)
  ·
    refine ⟨187895984130975773942926721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125263989420650515961951147 187895984130975773942926721)
    ·
      refine ⟨140921988098231830457195041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187895984130975773942926721 140921988098231830457195041)
      ·
        refine ⟨105691491073673872842896281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140921988098231830457195041 105691491073673872842896281)
        ·
          refine ⟨79268618305255404632172211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105691491073673872842896281 79268618305255404632172211)
          ·
            refine ⟨118902927457883106948258317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79268618305255404632172211 118902927457883106948258317)
            ·
              refine ⟨44588597796706165105596869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118902927457883106948258317 44588597796706165105596869)
              ·
                refine ⟨8360362086882405957299413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44588597796706165105596869 8360362086882405957299413)
                ·
                  refine ⟨195945986411306389624205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8360362086882405957299413 195945986411306389624205)
                  ·
                    rfl

theorem cell23_3434431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 7].length) (baseStart_3434431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434431 prefixEnd_3434431 := by exact prefixLift 3434431
  have htrace : WordTrace (prefixWord ++ tailWord_3434431) baseStart_3434431 baseEnd_3434431 := by
    simpa [prefixWord, tailWord_3434431, baseEnd_3434431] using wordTrace_append hprefix tailTrace_3434431
  have hstable : (prefixWord ++ tailWord_3434431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434431).length < 2 ^ (prefixWord ++ tailWord_3434431).sum := by decide
  have hdescent : baseEnd_3434431 < baseStart_3434431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434491 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 2, 8]
def baseStart_3434491 : Nat := 118140960795 + 3434491 * 2 ^ 59
def prefixEnd_3434491 : Nat := 4983230072969 + 3 ^ 40 * 3434491 * 2
def baseEnd_3434491 : Nat := 587848228847009090622523

theorem tailTrace_3434491 : CollatzResearch.WordTrace tailWord_3434491 prefixEnd_3434491 587848228847009090622523 := by
  unfold tailWord_3434491
  simp only [CollatzResearch.WordTrace]
  refine ⟨125266177800433146209135327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83510785200288764139423551 125266177800433146209135327)
  ·
    refine ⟨187899266700649719313702991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125266177800433146209135327 187899266700649719313702991)
    ·
      refine ⟨281848900050974578970554487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187899266700649719313702991 281848900050974578970554487)
      ·
        refine ⟨422773350076461868455831731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281848900050974578970554487 422773350076461868455831731)
        ·
          refine ⟨634160025114692802683747597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422773350076461868455831731 634160025114692802683747597)
          ·
            refine ⟨237810009418009801006405349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 634160025114692802683747597 237810009418009801006405349)
            ·
              refine ⟨44589376765876837688701003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237810009418009801006405349 44589376765876837688701003)
              ·
                refine ⟨66884065148815256533051505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44589376765876837688701003 66884065148815256533051505)
                ·
                  refine ⟨50163048861611442399788629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66884065148815256533051505 50163048861611442399788629)
                  ·
                    refine ⟨587848228847009090622523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50163048861611442399788629 587848228847009090622523)
                    ·
                      rfl

theorem cell23_3434491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 8].length) (baseStart_3434491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434491 prefixEnd_3434491 := by exact prefixLift 3434491
  have htrace : WordTrace (prefixWord ++ tailWord_3434491) baseStart_3434491 baseEnd_3434491 := by
    simpa [prefixWord, tailWord_3434491, baseEnd_3434491] using wordTrace_append hprefix tailTrace_3434491
  have hstable : (prefixWord ++ tailWord_3434491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434491).length < 2 ^ (prefixWord ++ tailWord_3434491).sum := by decide
  have hdescent : baseEnd_3434491 < baseStart_3434491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434542 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3434542 : Nat := 118140960795 + 3434542 * 2 ^ 59
def prefixEnd_3434542 : Nat := 4983230072969 + 3 ^ 40 * 3434542 * 2
def baseEnd_3434542 : Nat := 587856958018135524109945

theorem tailTrace_3434542 : CollatzResearch.WordTrace tailWord_3434542 prefixEnd_3434542 587856958018135524109945 := by
  unfold tailWord_3434542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15658504740406047739905235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83512025282165587946161253 15658504740406047739905235)
  ·
    refine ⟨23487757110609071609857853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15658504740406047739905235 23487757110609071609857853)
    ·
      refine ⟨8807908916478401853696695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23487757110609071609857853 8807908916478401853696695)
      ·
        refine ⟨13211863374717602780545043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8807908916478401853696695 13211863374717602780545043)
        ·
          refine ⟨19817795062076404170817565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13211863374717602780545043 19817795062076404170817565)
          ·
            refine ⟨7431673148278651564056587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19817795062076404170817565 7431673148278651564056587)
            ·
              refine ⟨11147509722417977346084881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7431673148278651564056587 11147509722417977346084881)
              ·
                refine ⟨8360632291813483009563661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11147509722417977346084881 8360632291813483009563661)
                ·
                  refine ⟨3135237109430056128586373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8360632291813483009563661 3135237109430056128586373)
                  ·
                    refine ⟨587856958018135524109945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3135237109430056128586373 587856958018135524109945)
                    ·
                      rfl

theorem cell23_3434542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3434542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434542 prefixEnd_3434542 := by exact prefixLift 3434542
  have htrace : WordTrace (prefixWord ++ tailWord_3434542) baseStart_3434542 baseEnd_3434542 := by
    simpa [prefixWord, tailWord_3434542, baseEnd_3434542] using wordTrace_append hprefix tailTrace_3434542
  have hstable : (prefixWord ++ tailWord_3434542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434542).length < 2 ^ (prefixWord ++ tailWord_3434542).sum := by decide
  have hdescent : baseEnd_3434542 < baseStart_3434542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434565 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 7, 1, 3]
def baseStart_3434565 : Nat := 118140960795 + 3434565 * 2 ^ 59
def prefixEnd_3434565 : Nat := 4983230072969 + 3 ^ 40 * 3434565 * 2
def baseEnd_3434565 : Nat := 1763582684109459982342229

theorem tailTrace_3434565 : CollatzResearch.WordTrace tailWord_3434565 prefixEnd_3434565 1763582684109459982342229 := by
  unfold tailWord_3434565
  simp only [CollatzResearch.WordTrace]
  refine ⟨125268876802165056847329149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83512584534776704564886099 125268876802165056847329149)
  ·
    refine ⟨46975828800811896317748431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125268876802165056847329149 46975828800811896317748431)
    ·
      refine ⟨70463743201217844476622647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46975828800811896317748431 70463743201217844476622647)
      ·
        refine ⟨105695614801826766714933971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70463743201217844476622647 105695614801826766714933971)
        ·
          refine ⟨158543422202740150072400957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105695614801826766714933971 158543422202740150072400957)
          ·
            refine ⟨59453783326027556277150359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158543422202740150072400957 59453783326027556277150359)
            ·
              refine ⟨89180674989041334415725539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59453783326027556277150359 89180674989041334415725539)
              ·
                refine ⟨133771012483562001623588309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89180674989041334415725539 133771012483562001623588309)
                ·
                  refine ⟨3135258105083484413052851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 133771012483562001623588309 3135258105083484413052851)
                  ·
                    refine ⟨4702887157625226619579277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3135258105083484413052851 4702887157625226619579277)
                    ·
                      refine ⟨1763582684109459982342229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4702887157625226619579277 1763582684109459982342229)
                      ·
                        rfl

theorem cell23_3434565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_3434565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434565 prefixEnd_3434565 := by exact prefixLift 3434565
  have htrace : WordTrace (prefixWord ++ tailWord_3434565) baseStart_3434565 baseEnd_3434565 := by
    simpa [prefixWord, tailWord_3434565, baseEnd_3434565] using wordTrace_append hprefix tailTrace_3434565
  have hstable : (prefixWord ++ tailWord_3434565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434565).length < 2 ^ (prefixWord ++ tailWord_3434565).sum := by decide
  have hdescent : baseEnd_3434565 < baseStart_3434565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434568 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 5, 5]
def baseStart_3434568 : Nat := 118140960795 + 3434568 * 2 ^ 59
def prefixEnd_3434568 : Nat := 4983230072969 + 3 ^ 40 * 3434568 * 2
def baseEnd_3434568 : Nat := 587861408183807823534905

theorem tailTrace_3434568 : CollatzResearch.WordTrace tailWord_3434568 prefixEnd_3434568 587861408183807823534905 := by
  unfold tailWord_3434568
  simp only [CollatzResearch.WordTrace]
  refine ⟨62634493110577094179844179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83512657480769458906458905 62634493110577094179844179)
  ·
    refine ⟨93951739665865641269766269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62634493110577094179844179 93951739665865641269766269)
    ·
      refine ⟨35231902374699615476162351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93951739665865641269766269 35231902374699615476162351)
      ·
        refine ⟨52847853562049423214243527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35231902374699615476162351 52847853562049423214243527)
        ·
          refine ⟨79271780343074134821365291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52847853562049423214243527 79271780343074134821365291)
          ·
            refine ⟨118907670514611202232047937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79271780343074134821365291 118907670514611202232047937)
            ·
              refine ⟨89180752885958401674035953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118907670514611202232047937 89180752885958401674035953)
              ·
                refine ⟨66885564664468801255526965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89180752885958401674035953 66885564664468801255526965)
                ·
                  refine ⟨6270521687293950117705653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66885564664468801255526965 6270521687293950117705653)
                  ·
                    refine ⟨587861408183807823534905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6270521687293950117705653 587861408183807823534905)
                    ·
                      rfl

theorem cell23_3434568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_3434568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434568 prefixEnd_3434568 := by exact prefixLift 3434568
  have htrace : WordTrace (prefixWord ++ tailWord_3434568) baseStart_3434568 baseEnd_3434568 := by
    simpa [prefixWord, tailWord_3434568, baseEnd_3434568] using wordTrace_append hprefix tailTrace_3434568
  have hstable : (prefixWord ++ tailWord_3434568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434568).length < 2 ^ (prefixWord ++ tailWord_3434568).sum := by decide
  have hdescent : baseEnd_3434568 < baseStart_3434568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434589 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 6]
def baseStart_3434589 : Nat := 118140960795 + 3434589 * 2 ^ 59
def prefixEnd_3434589 : Nat := 4983230072969 + 3 ^ 40 * 3434589 * 2
def baseEnd_3434589 : Nat := 195955000849463098715791

theorem tailTrace_3434589 : CollatzResearch.WordTrace tailWord_3434589 prefixEnd_3434589 195955000849463098715791 := by
  unfold tailWord_3434589
  simp only [CollatzResearch.WordTrace]
  refine ⟨125269752154078108946202821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83513168102718739297468547 125269752154078108946202821)
  ·
    refine ⟨23488078528889645427413029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125269752154078108946202821 23488078528889645427413029)
    ·
      refine ⟨4404014724166808517639943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23488078528889645427413029 4404014724166808517639943)
      ·
        refine ⟨6606022086250212776459915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4404014724166808517639943 6606022086250212776459915)
        ·
          refine ⟨9909033129375319164689873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6606022086250212776459915 9909033129375319164689873)
          ·
            refine ⟨7431774847031489373517405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9909033129375319164689873 7431774847031489373517405)
            ·
              refine ⟨2786915567636808515069027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7431774847031489373517405 2786915567636808515069027)
              ·
                refine ⟨4180373351455212772603541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786915567636808515069027 4180373351455212772603541)
                ·
                  refine ⟨195955000849463098715791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4180373351455212772603541 195955000849463098715791)
                  ·
                    rfl

theorem cell23_3434589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_3434589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434589 prefixEnd_3434589 := by exact prefixLift 3434589
  have htrace : WordTrace (prefixWord ++ tailWord_3434589) baseStart_3434589 baseEnd_3434589 := by
    simpa [prefixWord, tailWord_3434589, baseEnd_3434589] using wordTrace_append hprefix tailTrace_3434589
  have hstable : (prefixWord ++ tailWord_3434589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434589).length < 2 ^ (prefixWord ++ tailWord_3434589).sum := by decide
  have hdescent : baseEnd_3434589 < baseStart_3434589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434615 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 4, 4]
def baseStart_3434615 : Nat := 118140960795 + 3434615 * 2 ^ 59
def prefixEnd_3434615 : Nat := 4983230072969 + 3 ^ 40 * 3434615 * 2
def baseEnd_3434615 : Nat := 587869452714061595572333

theorem tailTrace_3434615 : CollatzResearch.WordTrace tailWord_3434615 prefixEnd_3434615 587869452714061595572333 := by
  unfold tailWord_3434615
  simp only [CollatzResearch.WordTrace]
  refine ⟨125270700451983915386649299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83513800301322610257766199 125270700451983915386649299)
  ·
    refine ⟨187906050677975873079973949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125270700451983915386649299 187906050677975873079973949)
    ·
      refine ⟨70464769004240952404990231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187906050677975873079973949 70464769004240952404990231)
      ·
        refine ⟨105697153506361428607485347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70464769004240952404990231 105697153506361428607485347)
        ·
          refine ⟨158545730259542142911228021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105697153506361428607485347 158545730259542142911228021)
          ·
            refine ⟨14863662211832075897927627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158545730259542142911228021 14863662211832075897927627)
            ·
              refine ⟨22295493317748113846891441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14863662211832075897927627 22295493317748113846891441)
              ·
                refine ⟨16721619988311085385168581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22295493317748113846891441 16721619988311085385168581)
                ·
                  refine ⟨3135303747808328509719109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16721619988311085385168581 3135303747808328509719109)
                  ·
                    refine ⟨587869452714061595572333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3135303747808328509719109 587869452714061595572333)
                    ·
                      rfl

theorem cell23_3434615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_3434615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434615 prefixEnd_3434615 := by exact prefixLift 3434615
  have htrace : WordTrace (prefixWord ++ tailWord_3434615) baseStart_3434615 baseEnd_3434615 := by
    simpa [prefixWord, tailWord_3434615, baseEnd_3434615] using wordTrace_append hprefix tailTrace_3434615
  have hstable : (prefixWord ++ tailWord_3434615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434615).length < 2 ^ (prefixWord ++ tailWord_3434615).sum := by decide
  have hdescent : baseEnd_3434615 < baseStart_3434615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434632 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 4, 4]
def baseStart_3434632 : Nat := 118140960795 + 3434632 * 2 ^ 59
def prefixEnd_3434632 : Nat := 4983230072969 + 3 ^ 40 * 3434632 * 2
def baseEnd_3434632 : Nat := 587872362437770406734807

theorem tailTrace_3434632 : CollatzResearch.WordTrace tailWord_3434632 prefixEnd_3434632 587872362437770406734807 := by
  unfold tailWord_3434632
  simp only [CollatzResearch.WordTrace]
  refine ⟨62635660246461163645009075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83514213661948218193345433 62635660246461163645009075)
  ·
    refine ⟨93953490369691745467513613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62635660246461163645009075 93953490369691745467513613)
    ·
      refine ⟨35232558888634404550317605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93953490369691745467513613 35232558888634404550317605)
      ·
        refine ⟨6606104791618950853184551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35232558888634404550317605 6606104791618950853184551)
        ·
          refine ⟨9909157187428426279776827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6606104791618950853184551 9909157187428426279776827)
          ·
            refine ⟨14863735781142639419665241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9909157187428426279776827 14863735781142639419665241)
            ·
              refine ⟨11147801835856979564748931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14863735781142639419665241 11147801835856979564748931)
              ·
                refine ⟨16721702753785469347123397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11147801835856979564748931 16721702753785469347123397)
                ·
                  refine ⟨3135319266334775502585637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16721702753785469347123397 3135319266334775502585637)
                  ·
                    refine ⟨587872362437770406734807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3135319266334775502585637 587872362437770406734807)
                    ·
                      rfl

theorem cell23_3434632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_3434632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434632 prefixEnd_3434632 := by exact prefixLift 3434632
  have htrace : WordTrace (prefixWord ++ tailWord_3434632) baseStart_3434632 baseEnd_3434632 := by
    simpa [prefixWord, tailWord_3434632, baseEnd_3434632] using wordTrace_append hprefix tailTrace_3434632
  have hstable : (prefixWord ++ tailWord_3434632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434632).length < 2 ^ (prefixWord ++ tailWord_3434632).sum := by decide
  have hdescent : baseEnd_3434632 < baseStart_3434632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434642 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_3434642 : Nat := 118140960795 + 3434642 * 2 ^ 59
def prefixEnd_3434642 : Nat := 4983230072969 + 3 ^ 40 * 3434642 * 2
def baseEnd_3434642 : Nat := 1763622222119856181079375

theorem tailTrace_3434642 : CollatzResearch.WordTrace tailWord_3434642 prefixEnd_3434642 1763622222119856181079375 := by
  unfold tailWord_3434642
  simp only [CollatzResearch.WordTrace]
  refine ⟨31317921305721524749470545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83514456815257399331921453 31317921305721524749470545)
  ·
    refine ⟨23488440979291143562102909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31317921305721524749470545 23488440979291143562102909)
    ·
      refine ⟨8808165367234178835788591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23488440979291143562102909 8808165367234178835788591)
      ·
        refine ⟨13212248050851268253682887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8808165367234178835788591 13212248050851268253682887)
        ·
          refine ⟨19818372076276902380524331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13212248050851268253682887 19818372076276902380524331)
          ·
            refine ⟨29727558114415353570786497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19818372076276902380524331 29727558114415353570786497)
            ·
              refine ⟨22295668585811515178089873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29727558114415353570786497 22295668585811515178089873)
              ·
                refine ⟨16721751439358636383567405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22295668585811515178089873 16721751439358636383567405)
                ·
                  refine ⟨6270656789759488643837777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16721751439358636383567405 6270656789759488643837777)
                  ·
                    refine ⟨4702992592319616482878333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6270656789759488643837777 4702992592319616482878333)
                    ·
                      refine ⟨1763622222119856181079375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4702992592319616482878333 1763622222119856181079375)
                      ·
                        rfl

theorem cell23_3434642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_3434642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434642 prefixEnd_3434642 := by exact prefixLift 3434642
  have htrace : WordTrace (prefixWord ++ tailWord_3434642) baseStart_3434642 baseEnd_3434642 := by
    simpa [prefixWord, tailWord_3434642, baseEnd_3434642] using wordTrace_append hprefix tailTrace_3434642
  have hstable : (prefixWord ++ tailWord_3434642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434642).length < 2 ^ (prefixWord ++ tailWord_3434642).sum := by decide
  have hdescent : baseEnd_3434642 < baseStart_3434642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434668 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_3434668 : Nat := 118140960795 + 3434668 * 2 ^ 59
def prefixEnd_3434668 : Nat := 4983230072969 + 3 ^ 40 * 3434668 * 2
def baseEnd_3434668 : Nat := 1763635572616873079354255

theorem tailTrace_3434668 : CollatzResearch.WordTrace tailWord_3434668 prefixEnd_3434668 1763635572616873079354255 := by
  unfold tailWord_3434668
  simp only [CollatzResearch.WordTrace]
  refine ⟨62636316760395952719164329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83515089013861270292219105 62636316760395952719164329)
  ·
    refine ⟨46977237570296964539373247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62636316760395952719164329 46977237570296964539373247)
    ·
      refine ⟨70465856355445446809059871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46977237570296964539373247 70465856355445446809059871)
      ·
        refine ⟨105698784533168170213589807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70465856355445446809059871 105698784533168170213589807)
        ·
          refine ⟨158548176799752255320384711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105698784533168170213589807 158548176799752255320384711)
          ·
            refine ⟨237822265199628382980577067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158548176799752255320384711 237822265199628382980577067)
            ·
              refine ⟨356733397799442574470865601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237822265199628382980577067 356733397799442574470865601)
              ·
                refine ⟨267550048349581930853149201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356733397799442574470865601 267550048349581930853149201)
                ·
                  refine ⟨200662536262186448139861901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267550048349581930853149201 200662536262186448139861901)
                  ·
                    refine ⟨75248451098319918052448213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200662536262186448139861901 75248451098319918052448213)
                    ·
                      refine ⟨1763635572616873079354255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75248451098319918052448213 1763635572616873079354255)
                      ·
                        rfl

theorem cell23_3434668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_3434668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434668 prefixEnd_3434668 := by exact prefixLift 3434668
  have htrace : WordTrace (prefixWord ++ tailWord_3434668) baseStart_3434668 baseEnd_3434668 := by
    simpa [prefixWord, tailWord_3434668, baseEnd_3434668] using wordTrace_append hprefix tailTrace_3434668
  have hstable : (prefixWord ++ tailWord_3434668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434668).length < 2 ^ (prefixWord ++ tailWord_3434668).sum := by decide
  have hdescent : baseEnd_3434668 < baseStart_3434668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434742 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3434742 : Nat := 118140960795 + 3434742 * 2 ^ 59
def prefixEnd_3434742 : Nat := 4983230072969 + 3 ^ 40 * 3434742 * 2
def baseEnd_3434742 : Nat := 1763673570185305789828915

theorem tailTrace_3434742 : CollatzResearch.WordTrace tailWord_3434742 prefixEnd_3434742 1763673570185305789828915 := by
  unfold tailWord_3434742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7829708282657738504782655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83516888348349210717681653 7829708282657738504782655)
  ·
    refine ⟨11744562423986607757173983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7829708282657738504782655 11744562423986607757173983)
    ·
      refine ⟨17616843635979911635760975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11744562423986607757173983 17616843635979911635760975)
      ·
        refine ⟨26425265453969867453641463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17616843635979911635760975 26425265453969867453641463)
        ·
          refine ⟨39637898180954801180462195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26425265453969867453641463 39637898180954801180462195)
          ·
            refine ⟨59456847271432201770693293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39637898180954801180462195 59456847271432201770693293)
            ·
              refine ⟨22296317726787075664009985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59456847271432201770693293 22296317726787075664009985)
              ·
                refine ⟨16722238295090306748007489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22296317726787075664009985 16722238295090306748007489)
                ·
                  refine ⟨12541678721317730061005617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16722238295090306748007489 12541678721317730061005617)
                  ·
                    refine ⟨9406259040988297545754213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12541678721317730061005617 9406259040988297545754213)
                    ·
                      refine ⟨1763673570185305789828915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9406259040988297545754213 1763673570185305789828915)
                      ·
                        rfl

theorem cell23_3434742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3434742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434742 prefixEnd_3434742 := by exact prefixLift 3434742
  have htrace : WordTrace (prefixWord ++ tailWord_3434742) baseStart_3434742 baseEnd_3434742 := by
    simpa [prefixWord, tailWord_3434742, baseEnd_3434742] using wordTrace_append hprefix tailTrace_3434742
  have hstable : (prefixWord ++ tailWord_3434742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434742).length < 2 ^ (prefixWord ++ tailWord_3434742).sum := by decide
  have hdescent : baseEnd_3434742 < baseStart_3434742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434746 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2]
def baseStart_3434746 : Nat := 118140960795 + 3434746 * 2 ^ 59
def prefixEnd_3434746 : Nat := 4983230072969 + 3 ^ 40 * 3434746 * 2
def baseEnd_3434746 : Nat := 1763675624107923774178897

theorem tailTrace_3434746 : CollatzResearch.WordTrace tailWord_3434746 prefixEnd_3434746 1763675624107923774178897 := by
  unfold tailWord_3434746
  simp only [CollatzResearch.WordTrace]
  refine ⟨31318869603627331189917023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83516985609672883173112061 31318869603627331189917023)
  ·
    refine ⟨46978304405440996784875535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31318869603627331189917023 46978304405440996784875535)
    ·
      refine ⟨70467456608161495177313303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46978304405440996784875535 70467456608161495177313303)
      ·
        refine ⟨105701184912242242765969955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70467456608161495177313303 105701184912242242765969955)
        ·
          refine ⟨158551777368363364148954933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105701184912242242765969955 158551777368363364148954933)
          ·
            refine ⟨14864229128284065388964525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158551777368363364148954933 14864229128284065388964525)
            ·
              refine ⟨5574085923106524520861697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14864229128284065388964525 5574085923106524520861697)
              ·
                refine ⟨4180564442329893390646273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5574085923106524520861697 4180564442329893390646273)
                ·
                  refine ⟨3135423331747420042984705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4180564442329893390646273 3135423331747420042984705)
                  ·
                    refine ⟨2351567498810565032238529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3135423331747420042984705 2351567498810565032238529)
                    ·
                      refine ⟨1763675624107923774178897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2351567498810565032238529 1763675624107923774178897)
                      ·
                        rfl

theorem cell23_3434746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2].length) (baseStart_3434746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434746 prefixEnd_3434746 := by exact prefixLift 3434746
  have htrace : WordTrace (prefixWord ++ tailWord_3434746) baseStart_3434746 baseEnd_3434746 := by
    simpa [prefixWord, tailWord_3434746, baseEnd_3434746] using wordTrace_append hprefix tailTrace_3434746
  have hstable : (prefixWord ++ tailWord_3434746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434746).length < 2 ^ (prefixWord ++ tailWord_3434746).sum := by decide
  have hdescent : baseEnd_3434746 < baseStart_3434746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434752 : List Nat := [2, 1, 1, 2, 1, 1, 6, 4, 5]
def baseStart_3434752 : Nat := 118140960795 + 3434752 * 2 ^ 59
def prefixEnd_3434752 : Nat := 4983230072969 + 3 ^ 40 * 3434752 * 2
def baseEnd_3434752 : Nat := 195964300554650083411541

theorem tailTrace_3434752 : CollatzResearch.WordTrace tailWord_3434752 prefixEnd_3434752 195964300554650083411541 := by
  unfold tailWord_3434752
  simp only [CollatzResearch.WordTrace]
  refine ⟨62637848626243793892193255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83517131501658391856257673 62637848626243793892193255)
  ·
    refine ⟨93956772939365690838289883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62637848626243793892193255 93956772939365690838289883)
    ·
      refine ⟨140935159409048536257434825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93956772939365690838289883 140935159409048536257434825)
      ·
        refine ⟨105701369556786402193076119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140935159409048536257434825 105701369556786402193076119)
        ·
          refine ⟨158552054335179603289614179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105701369556786402193076119 158552054335179603289614179)
          ·
            refine ⟨237828081502769404934421269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158552054335179603289614179 237828081502769404934421269)
            ·
              refine ⟨11148191320442315856300997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237828081502769404934421269 11148191320442315856300997)
              ·
                refine ⟨2090285872582934223056437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11148191320442315856300997 2090285872582934223056437)
                ·
                  refine ⟨195964300554650083411541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2090285872582934223056437 195964300554650083411541)
                  ·
                    rfl

theorem cell23_3434752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 5].length) (baseStart_3434752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434752 prefixEnd_3434752 := by exact prefixLift 3434752
  have htrace : WordTrace (prefixWord ++ tailWord_3434752) baseStart_3434752 baseEnd_3434752 := by
    simpa [prefixWord, tailWord_3434752, baseEnd_3434752] using wordTrace_append hprefix tailTrace_3434752
  have hstable : (prefixWord ++ tailWord_3434752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434752).length < 2 ^ (prefixWord ++ tailWord_3434752).sum := by decide
  have hdescent : baseEnd_3434752 < baseStart_3434752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434762 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_3434762 : Nat := 118140960795 + 3434762 * 2 ^ 59
def prefixEnd_3434762 : Nat := 4983230072969 + 3 ^ 40 * 3434762 * 2
def baseEnd_3434762 : Nat := 1763683839798395711578823

theorem tailTrace_3434762 : CollatzResearch.WordTrace tailWord_3434762 prefixEnd_3434762 1763683839798395711578823 := by
  unfold tailWord_3434762
  simp only [CollatzResearch.WordTrace]
  refine ⟨31319015495612839873062635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83517374654967572994833693 31319015495612839873062635)
  ·
    refine ⟨46978523243419259809593953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31319015495612839873062635 46978523243419259809593953)
    ·
      refine ⟨35233892432564444857195465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46978523243419259809593953 35233892432564444857195465)
      ·
        refine ⟨26425419324423333642896599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35233892432564444857195465 26425419324423333642896599)
        ·
          refine ⟨39638128986635000464344899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26425419324423333642896599 39638128986635000464344899)
          ·
            refine ⟨59457193479952500696517349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39638128986635000464344899 59457193479952500696517349)
            ·
              refine ⟨11148223777491093880597003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59457193479952500696517349 11148223777491093880597003)
              ·
                refine ⟨16722335666236640820895505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11148223777491093880597003 16722335666236640820895505)
                ·
                  refine ⟨12541751749677480615671629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16722335666236640820895505 12541751749677480615671629)
                  ·
                    refine ⟨4703156906129055230876861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12541751749677480615671629 4703156906129055230876861)
                    ·
                      refine ⟨1763683839798395711578823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4703156906129055230876861 1763683839798395711578823)
                      ·
                        rfl

theorem cell23_3434762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_3434762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434762 prefixEnd_3434762 := by exact prefixLift 3434762
  have htrace : WordTrace (prefixWord ++ tailWord_3434762) baseStart_3434762 baseEnd_3434762 := by
    simpa [prefixWord, tailWord_3434762, baseEnd_3434762] using wordTrace_append hprefix tailTrace_3434762
  have hstable : (prefixWord ++ tailWord_3434762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434762).length < 2 ^ (prefixWord ++ tailWord_3434762).sum := by decide
  have hdescent : baseEnd_3434762 < baseStart_3434762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434786 : List Nat := [3, 3, 1, 1, 3, 3, 1, 3, 5]
def baseStart_3434786 : Nat := 118140960795 + 3434786 * 2 ^ 59
def prefixEnd_3434786 : Nat := 4983230072969 + 3 ^ 40 * 3434786 * 2
def baseEnd_3434786 : Nat := 195966240370455957519857

theorem tailTrace_3434786 : CollatzResearch.WordTrace tailWord_3434786 prefixEnd_3434786 195966240370455957519857 := by
  unfold tailWord_3434786
  simp only [CollatzResearch.WordTrace]
  refine ⟨31319234333591102897781053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83517958222909607727416141 31319234333591102897781053)
  ·
    refine ⟨11744712875096663586667895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31319234333591102897781053 11744712875096663586667895)
    ·
      refine ⟨17617069312644995380001843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11744712875096663586667895 17617069312644995380001843)
      ·
        refine ⟨26425603968967493070002765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17617069312644995380001843 26425603968967493070002765)
        ·
          refine ⟨9909601488362809901251037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26425603968967493070002765 9909601488362809901251037)
          ·
            refine ⟨3716100558136053712969139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9909601488362809901251037 3716100558136053712969139)
            ·
              refine ⟨5574150837204080569453709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716100558136053712969139 5574150837204080569453709)
              ·
                refine ⟨2090306563951530213545141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5574150837204080569453709 2090306563951530213545141)
                ·
                  refine ⟨195966240370455957519857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2090306563951530213545141 195966240370455957519857)
                  ·
                    rfl

theorem cell23_3434786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_3434786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434786 prefixEnd_3434786 := by exact prefixLift 3434786
  have htrace : WordTrace (prefixWord ++ tailWord_3434786) baseStart_3434786 baseEnd_3434786 := by
    simpa [prefixWord, tailWord_3434786, baseEnd_3434786] using wordTrace_append hprefix tailTrace_3434786
  have hstable : (prefixWord ++ tailWord_3434786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434786).length < 2 ^ (prefixWord ++ tailWord_3434786).sum := by decide
  have hdescent : baseEnd_3434786 < baseStart_3434786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434839 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 3]
def baseStart_3434839 : Nat := 118140960795 + 3434839 * 2 ^ 59
def prefixEnd_3434839 : Nat := 4983230072969 + 3 ^ 40 * 3434839 * 2
def baseEnd_3434839 : Nat := 1763723377808791910315969

theorem tailTrace_3434839 : CollatzResearch.WordTrace tailWord_3434839 prefixEnd_3434839 1763723377808791910315969 := by
  unfold tailWord_3434839
  simp only [CollatzResearch.WordTrace]
  refine ⟨125278870403172401642803571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83519246935448267761869047 125278870403172401642803571)
  ·
    refine ⟨187918305604758602464205357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125278870403172401642803571 187918305604758602464205357)
    ·
      refine ⟨70469364601784475924077009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187918305604758602464205357 70469364601784475924077009)
      ·
        refine ⟨52852023451338356943057757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70469364601784475924077009 52852023451338356943057757)
        ·
          refine ⟨19819508794251883853646659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52852023451338356943057757 19819508794251883853646659)
          ·
            refine ⟨29729263191377825780469989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19819508794251883853646659 29729263191377825780469989)
            ·
              refine ⟨5574236848383342333838123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29729263191377825780469989 5574236848383342333838123)
              ·
                refine ⟨8361355272575013500757185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5574236848383342333838123 8361355272575013500757185)
                ·
                  refine ⟨6271016454431260125567889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8361355272575013500757185 6271016454431260125567889)
                  ·
                    refine ⟨4703262340823445094175917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6271016454431260125567889 4703262340823445094175917)
                    ·
                      refine ⟨1763723377808791910315969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4703262340823445094175917 1763723377808791910315969)
                      ·
                        rfl

theorem cell23_3434839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_3434839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434839 prefixEnd_3434839 := by exact prefixLift 3434839
  have htrace : WordTrace (prefixWord ++ tailWord_3434839) baseStart_3434839 baseEnd_3434839 := by
    simpa [prefixWord, tailWord_3434839, baseEnd_3434839] using wordTrace_append hprefix tailTrace_3434839
  have hstable : (prefixWord ++ tailWord_3434839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434839).length < 2 ^ (prefixWord ++ tailWord_3434839).sum := by decide
  have hdescent : baseEnd_3434839 < baseStart_3434839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434890 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3434890 : Nat := 118140960795 + 3434890 * 2 ^ 59
def prefixEnd_3434890 : Nat := 4983230072969 + 3 ^ 40 * 3434890 * 2
def baseEnd_3434890 : Nat := 1763749565322171210778235

theorem tailTrace_3434890 : CollatzResearch.WordTrace tailWord_3434890 prefixEnd_3434890 1763749565322171210778235 := by
  unfold tailWord_3434890
  simp only [CollatzResearch.WordTrace]
  refine ⟨31320182631496909338227531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83520487017325091568606749 31320182631496909338227531)
  ·
    refine ⟨46980273947245364007341297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31320182631496909338227531 46980273947245364007341297)
    ·
      refine ⟨35235205460434023005505973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46980273947245364007341297 35235205460434023005505973)
      ·
        refine ⟨3303300511915689656766185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35235205460434023005505973 3303300511915689656766185)
        ·
          refine ⟨2477475383936767242574639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3303300511915689656766185 2477475383936767242574639)
          ·
            refine ⟨3716213075905150863861959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477475383936767242574639 3716213075905150863861959)
            ·
              refine ⟨5574319613857726295792939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716213075905150863861959 5574319613857726295792939)
              ·
                refine ⟨8361479420786589443689409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5574319613857726295792939 8361479420786589443689409)
                ·
                  refine ⟨6271109565589942082767057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8361479420786589443689409 6271109565589942082767057)
                  ·
                    refine ⟨4703332174192456562075293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6271109565589942082767057 4703332174192456562075293)
                    ·
                      refine ⟨1763749565322171210778235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4703332174192456562075293 1763749565322171210778235)
                      ·
                        rfl

theorem cell23_3434890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3434890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434890 prefixEnd_3434890 := by exact prefixLift 3434890
  have htrace : WordTrace (prefixWord ++ tailWord_3434890) baseStart_3434890 baseEnd_3434890 := by
    simpa [prefixWord, tailWord_3434890, baseEnd_3434890] using wordTrace_append hprefix tailTrace_3434890
  have hstable : (prefixWord ++ tailWord_3434890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434890).length < 2 ^ (prefixWord ++ tailWord_3434890).sum := by decide
  have hdescent : baseEnd_3434890 < baseStart_3434890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434906 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 1, 5]
def baseStart_3434906 : Nat := 118140960795 + 3434906 * 2 ^ 59
def prefixEnd_3434906 : Nat := 4983230072969 + 3 ^ 40 * 3434906 * 2
def baseEnd_3434906 : Nat := 587919260337547716059387

theorem tailTrace_3434906 : CollatzResearch.WordTrace tailWord_3434906 prefixEnd_3434906 587919260337547716059387 := by
  unfold tailWord_3434906
  simp only [CollatzResearch.WordTrace]
  refine ⟨31320328523482418021373143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83520876062619781390328381 31320328523482418021373143)
  ·
    refine ⟨46980492785223627032059715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31320328523482418021373143 46980492785223627032059715)
    ·
      refine ⟨70470739177835440548089573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46980492785223627032059715 70470739177835440548089573)
      ·
        refine ⟨13213263595844145102766795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70470739177835440548089573 13213263595844145102766795)
        ·
          refine ⟨19819895393766217654150193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13213263595844145102766795 19819895393766217654150193)
          ·
            refine ⟨14864921545324663240612645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19819895393766217654150193 14864921545324663240612645)
            ·
              refine ⟨2787172789748374357614871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14864921545324663240612645 2787172789748374357614871)
              ·
                refine ⟨4180759184622561536422307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787172789748374357614871 4180759184622561536422307)
                ·
                  refine ⟨6271138776933842304633461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180759184622561536422307 6271138776933842304633461)
                  ·
                    refine ⟨587919260337547716059387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6271138776933842304633461 587919260337547716059387)
                    ·
                      rfl

theorem cell23_3434906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_3434906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434906 prefixEnd_3434906 := by exact prefixLift 3434906
  have htrace : WordTrace (prefixWord ++ tailWord_3434906) baseStart_3434906 baseEnd_3434906 := by
    simpa [prefixWord, tailWord_3434906, baseEnd_3434906] using wordTrace_append hprefix tailTrace_3434906
  have hstable : (prefixWord ++ tailWord_3434906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434906).length < 2 ^ (prefixWord ++ tailWord_3434906).sum := by decide
  have hdescent : baseEnd_3434906 < baseStart_3434906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434920 : List Nat := [2, 1, 6, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_3434920 : Nat := 118140960795 + 3434920 * 2 ^ 59
def prefixEnd_3434920 : Nat := 4983230072969 + 3 ^ 40 * 3434920 * 2
def baseEnd_3434920 : Nat := 1763764969741806093403097

theorem tailTrace_3434920 : CollatzResearch.WordTrace tailWord_3434920 prefixEnd_3434920 1763764969741806093403097 := by
  unfold tailWord_3434920
  simp only [CollatzResearch.WordTrace]
  refine ⟨62640912357939476238251107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83521216477252634984334809 62640912357939476238251107)
  ·
    refine ⟨93961368536909214357376661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62640912357939476238251107 93961368536909214357376661)
    ·
      refine ⟨4404439150167619423002031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93961368536909214357376661 4404439150167619423002031)
      ·
        refine ⟨6606658725251429134503047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4404439150167619423002031 6606658725251429134503047)
        ·
          refine ⟨9909988087877143701754571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6606658725251429134503047 9909988087877143701754571)
          ·
            refine ⟨14864982131815715552631857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9909988087877143701754571 14864982131815715552631857)
            ·
              refine ⟨11148736598861786664473893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14864982131815715552631857 11148736598861786664473893)
              ·
                refine ⟨2090388112286584999588855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11148736598861786664473893 2090388112286584999588855)
                ·
                  refine ⟨3135582168429877499383283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090388112286584999588855 3135582168429877499383283)
                  ·
                    refine ⟨4703373252644816249074925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3135582168429877499383283 4703373252644816249074925)
                    ·
                      refine ⟨1763764969741806093403097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4703373252644816249074925 1763764969741806093403097)
                      ·
                        rfl

theorem cell23_3434920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_3434920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434920 prefixEnd_3434920 := by exact prefixLift 3434920
  have htrace : WordTrace (prefixWord ++ tailWord_3434920) baseStart_3434920 baseEnd_3434920 := by
    simpa [prefixWord, tailWord_3434920, baseEnd_3434920] using wordTrace_append hprefix tailTrace_3434920
  have hstable : (prefixWord ++ tailWord_3434920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434920).length < 2 ^ (prefixWord ++ tailWord_3434920).sum := by decide
  have hdescent : baseEnd_3434920 < baseStart_3434920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434929 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3434929 : Nat := 118140960795 + 3434929 * 2 ^ 59
def prefixEnd_3434929 : Nat := 4983230072969 + 3 ^ 40 * 3434929 * 2
def baseEnd_3434929 : Nat := 1763769591067696558190555

theorem tailTrace_3434929 : CollatzResearch.WordTrace tailWord_3434929 prefixEnd_3434929 1763769591067696558190555 := by
  unfold tailWord_3434929
  simp only [CollatzResearch.WordTrace]
  refine ⟨125282152972846347013579841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83521435315230898009053227 125282152972846347013579841)
  ·
    refine ⟨93961614729634760260184881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125282152972846347013579841 93961614729634760260184881)
    ·
      refine ⟨70471211047226070195138661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93961614729634760260184881 70471211047226070195138661)
      ·
        refine ⟨13213352071354888161588499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70471211047226070195138661 13213352071354888161588499)
        ·
          refine ⟨19820028107032332242382749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13213352071354888161588499 19820028107032332242382749)
          ·
            refine ⟨7432510540137124590893531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19820028107032332242382749 7432510540137124590893531)
            ·
              refine ⟨11148765810205686886340297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7432510540137124590893531 11148765810205686886340297)
              ·
                refine ⟨8361574357654265164755223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11148765810205686886340297 8361574357654265164755223)
                ·
                  refine ⟨12542361536481397747132835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8361574357654265164755223 12542361536481397747132835)
                  ·
                    refine ⟨18813542304722096620699253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12542361536481397747132835 18813542304722096620699253)
                    ·
                      refine ⟨1763769591067696558190555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18813542304722096620699253 1763769591067696558190555)
                      ·
                        rfl

theorem cell23_3434929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3434929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434929 prefixEnd_3434929 := by exact prefixLift 3434929
  have htrace : WordTrace (prefixWord ++ tailWord_3434929) baseStart_3434929 baseEnd_3434929 := by
    simpa [prefixWord, tailWord_3434929, baseEnd_3434929] using wordTrace_append hprefix tailTrace_3434929
  have hstable : (prefixWord ++ tailWord_3434929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434929).length < 2 ^ (prefixWord ++ tailWord_3434929).sum := by decide
  have hdescent : baseEnd_3434929 < baseStart_3434929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434976 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 2, 1, 3]
def baseStart_3434976 : Nat := 118140960795 + 3434976 * 2 ^ 59
def prefixEnd_3434976 : Nat := 4983230072969 + 3 ^ 40 * 3434976 * 2
def baseEnd_3434976 : Nat := 1763793724658457874302839

theorem tailTrace_3434976 : CollatzResearch.WordTrace tailWord_3434976 prefixEnd_3434976 1763793724658457874302839 := by
  unfold tailWord_3434976
  simp only [CollatzResearch.WordTrace]
  refine ⟨62641933601838037020270391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83522578135784049360360521 62641933601838037020270391)
  ·
    refine ⟨93962900402757055530405587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62641933601838037020270391 93962900402757055530405587)
    ·
      refine ⟨140944350604135583295608381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93962900402757055530405587 140944350604135583295608381)
      ·
        refine ⟨52854131476550843735853143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140944350604135583295608381 52854131476550843735853143)
        ·
          refine ⟨79281197214826265603779715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52854131476550843735853143 79281197214826265603779715)
          ·
            refine ⟨118921795822239398405669573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79281197214826265603779715 118921795822239398405669573)
            ·
              refine ⟨22297836716669887201063045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118921795822239398405669573 22297836716669887201063045)
              ·
                refine ⟨4180844384375603850199321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22297836716669887201063045 4180844384375603850199321)
                ·
                  refine ⟨3135633288281702887649491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4180844384375603850199321 3135633288281702887649491)
                  ·
                    refine ⟨4703449932422554331474237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3135633288281702887649491 4703449932422554331474237)
                    ·
                      refine ⟨1763793724658457874302839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4703449932422554331474237 1763793724658457874302839)
                      ·
                        rfl

theorem cell23_3434976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_3434976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434976 prefixEnd_3434976 := by exact prefixLift 3434976
  have htrace : WordTrace (prefixWord ++ tailWord_3434976) baseStart_3434976 baseEnd_3434976 := by
    simpa [prefixWord, tailWord_3434976, baseEnd_3434976] using wordTrace_append hprefix tailTrace_3434976
  have hstable : (prefixWord ++ tailWord_3434976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434976).length < 2 ^ (prefixWord ++ tailWord_3434976).sum := by decide
  have hdescent : baseEnd_3434976 < baseStart_3434976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434992 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 1, 8]
def baseStart_3434992 : Nat := 118140960795 + 3434992 * 2 ^ 59
def prefixEnd_3434992 : Nat := 4983230072969 + 3 ^ 40 * 3434992 * 2
def baseEnd_3434992 : Nat := 587933980116309937234255

theorem tailTrace_3434992 : CollatzResearch.WordTrace tailWord_3434992 prefixEnd_3434992 587933980116309937234255 := by
  unfold tailWord_3434992
  simp only [CollatzResearch.WordTrace]
  refine ⟨62642225385809054386561615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83522967181078739182082153 62642225385809054386561615)
  ·
    refine ⟨93963338078713581579842423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62642225385809054386561615 93963338078713581579842423)
    ·
      refine ⟨140945007118070372369763635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93963338078713581579842423 140945007118070372369763635)
      ·
        refine ⟨211417510677105558554645453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140945007118070372369763635 211417510677105558554645453)
        ·
          refine ⟨79281566503914584457992045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211417510677105558554645453 79281566503914584457992045)
          ·
            refine ⟨29730587438967969171747017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79281566503914584457992045 29730587438967969171747017)
            ·
              refine ⟨22297940579225976878810263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29730587438967969171747017 22297940579225976878810263)
              ·
                refine ⟨33446910868838965318215395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22297940579225976878810263 33446910868838965318215395)
                ·
                  refine ⟨50170366303258447977323093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33446910868838965318215395 50170366303258447977323093)
                  ·
                    refine ⟨587933980116309937234255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50170366303258447977323093 587933980116309937234255)
                    ·
                      rfl

theorem cell23_3434992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_3434992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434992 prefixEnd_3434992 := by exact prefixLift 3434992
  have htrace : WordTrace (prefixWord ++ tailWord_3434992) baseStart_3434992 baseEnd_3434992 := by
    simpa [prefixWord, tailWord_3434992, baseEnd_3434992] using wordTrace_append hprefix tailTrace_3434992
  have hstable : (prefixWord ++ tailWord_3434992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434992).length < 2 ^ (prefixWord ++ tailWord_3434992).sum := by decide
  have hdescent : baseEnd_3434992 < baseStart_3434992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434997 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3434997 : Nat := 118140960795 + 3434997 * 2 ^ 59
def prefixEnd_3434997 : Nat := 4983230072969 + 3 ^ 40 * 3434997 * 2
def baseEnd_3434997 : Nat := 1763804507752202292140243

theorem tailTrace_3434997 : CollatzResearch.WordTrace tailWord_3434997 prefixEnd_3434997 1763804507752202292140243 := by
  unfold tailWord_3434997
  simp only [CollatzResearch.WordTrace]
  refine ⟨125284633136599994627055245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83523088757733329751370163 125284633136599994627055245)
  ·
    refine ⟨46981737426224997985145717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125284633136599994627055245 46981737426224997985145717)
    ·
      refine ⟨4404537883708593561107411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46981737426224997985145717 4404537883708593561107411)
      ·
        refine ⟨6606806825562890341661117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4404537883708593561107411 6606806825562890341661117)
        ·
          refine ⟨2477552559586083878122919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6606806825562890341661117 2477552559586083878122919)
          ·
            refine ⟨3716328839379125817184379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477552559586083878122919 3716328839379125817184379)
            ·
              refine ⟨5574493259068688725776569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716328839379125817184379 5574493259068688725776569)
              ·
                refine ⟨4180869944301516544332427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5574493259068688725776569 4180869944301516544332427)
                ·
                  refine ⟨6271304916452274816498641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180869944301516544332427 6271304916452274816498641)
                  ·
                    refine ⟨4703478687339206112373981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6271304916452274816498641 4703478687339206112373981)
                    ·
                      refine ⟨1763804507752202292140243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4703478687339206112373981 1763804507752202292140243)
                      ·
                        rfl

theorem cell23_3434997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3434997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3434997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3434997 prefixEnd_3434997 := by exact prefixLift 3434997
  have htrace : WordTrace (prefixWord ++ tailWord_3434997) baseStart_3434997 baseEnd_3434997 := by
    simpa [prefixWord, tailWord_3434997, baseEnd_3434997] using wordTrace_append hprefix tailTrace_3434997
  have hstable : (prefixWord ++ tailWord_3434997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434997).length < 2 ^ (prefixWord ++ tailWord_3434997).sum := by decide
  have hdescent : baseEnd_3434997 < baseStart_3434997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435014 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_3435014 : Nat := 118140960795 + 3435014 * 2 ^ 59
def prefixEnd_3435014 : Nat := 4983230072969 + 3 ^ 40 * 3435014 * 2
def baseEnd_3435014 : Nat := 1763813236923328725627665

theorem tailTrace_3435014 : CollatzResearch.WordTrace tailWord_3435014 prefixEnd_3435014 1763813236923328725627665 := by
  unfold tailWord_3435014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915164161798075204075753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83523502118358937686949397 3915164161798075204075753)
  ·
    refine ⟨2936373121348556403056815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3915164161798075204075753 2936373121348556403056815)
    ·
      refine ⟨4404559682022834604585223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2936373121348556403056815 4404559682022834604585223)
      ·
        refine ⟨6606839523034251906877835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4404559682022834604585223 6606839523034251906877835)
        ·
          refine ⟨9910259284551377860316753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6606839523034251906877835 9910259284551377860316753)
          ·
            refine ⟨7432694463413533395237565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9910259284551377860316753 7432694463413533395237565)
            ·
              refine ⟨2787260423780075023214087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7432694463413533395237565 2787260423780075023214087)
              ·
                refine ⟨4180890635670112534821131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787260423780075023214087 4180890635670112534821131)
                ·
                  refine ⟨6271335953505168802231697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180890635670112534821131 6271335953505168802231697)
                  ·
                    refine ⟨4703501965128876601673773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6271335953505168802231697 4703501965128876601673773)
                    ·
                      refine ⟨1763813236923328725627665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4703501965128876601673773 1763813236923328725627665)
                      ·
                        rfl

theorem cell23_3435014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_3435014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435014 prefixEnd_3435014 := by exact prefixLift 3435014
  have htrace : WordTrace (prefixWord ++ tailWord_3435014) baseStart_3435014 baseEnd_3435014 := by
    simpa [prefixWord, tailWord_3435014, baseEnd_3435014] using wordTrace_append hprefix tailTrace_3435014
  have hstable : (prefixWord ++ tailWord_3435014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435014).length < 2 ^ (prefixWord ++ tailWord_3435014).sum := by decide
  have hdescent : baseEnd_3435014 < baseStart_3435014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435019 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 5]
def baseStart_3435019 : Nat := 118140960795 + 3435019 * 2 ^ 59
def prefixEnd_3435019 : Nat := 4983230072969 + 3 ^ 40 * 3435019 * 2
def baseEnd_3435019 : Nat := 1763815804326601206065141

theorem tailTrace_3435019 : CollatzResearch.WordTrace tailWord_3435019 prefixEnd_3435019 1763815804326601206065141 := by
  unfold tailWord_3435019
  simp only [CollatzResearch.WordTrace]
  refine ⟨125285435542520292384356111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83523623695013528256237407 125285435542520292384356111)
  ·
    refine ⟨187928153313780438576534167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125285435542520292384356111 187928153313780438576534167)
    ·
      refine ⟨281892229970670657864801251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187928153313780438576534167 281892229970670657864801251)
      ·
        refine ⟨422838344956005986797201877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281892229970670657864801251 422838344956005986797201877)
        ·
          refine ⟨9910273709906390315559419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 422838344956005986797201877 9910273709906390315559419)
          ·
            refine ⟨14865410564859585473339129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9910273709906390315559419 14865410564859585473339129)
            ·
              refine ⟨11149057923644689105004347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14865410564859585473339129 11149057923644689105004347)
              ·
                refine ⟨16723586885467033657506521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11149057923644689105004347 16723586885467033657506521)
                ·
                  refine ⟨12542690164100275243129891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16723586885467033657506521 12542690164100275243129891)
                  ·
                    refine ⟨18814035246150412864694837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12542690164100275243129891 18814035246150412864694837)
                    ·
                      refine ⟨1763815804326601206065141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18814035246150412864694837 1763815804326601206065141)
                      ·
                        rfl

theorem cell23_3435019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 5].length) (baseStart_3435019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435019 prefixEnd_3435019 := by exact prefixLift 3435019
  have htrace : WordTrace (prefixWord ++ tailWord_3435019) baseStart_3435019 baseEnd_3435019 := by
    simpa [prefixWord, tailWord_3435019, baseEnd_3435019] using wordTrace_append hprefix tailTrace_3435019
  have hstable : (prefixWord ++ tailWord_3435019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435019).length < 2 ^ (prefixWord ++ tailWord_3435019).sum := by decide
  have hdescent : baseEnd_3435019 < baseStart_3435019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435020 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 1, 3, 2]
def baseStart_3435020 : Nat := 118140960795 + 3435020 * 2 ^ 59
def prefixEnd_3435020 : Nat := 4983230072969 + 3 ^ 40 * 3435020 * 2
def baseEnd_3435020 : Nat := 1763816317807255702152637

theorem tailTrace_3435020 : CollatzResearch.WordTrace tailWord_3435020 prefixEnd_3435020 1763816317807255702152637 := by
  unfold tailWord_3435020
  simp only [CollatzResearch.WordTrace]
  refine ⟨62642736007758334777571257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83523648010344446370095009 62642736007758334777571257)
  ·
    refine ⟨46982052005818751083178443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62642736007758334777571257 46982052005818751083178443)
    ·
      refine ⟨70473078008728126624767665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46982052005818751083178443 70473078008728126624767665)
      ·
        refine ⟨52854808506546094968575749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70473078008728126624767665 52854808506546094968575749)
        ·
          refine ⟨9910276594977392806607953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52854808506546094968575749 9910276594977392806607953)
          ·
            refine ⟨7432707446233044604955965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9910276594977392806607953 7432707446233044604955965)
            ·
              refine ⟨2787265292337391726858487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7432707446233044604955965 2787265292337391726858487)
              ·
                refine ⟨4180897938506087590287731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787265292337391726858487 4180897938506087590287731)
                ·
                  refine ⟨6271346907759131385431597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180897938506087590287731 6271346907759131385431597)
                  ·
                    refine ⟨2351755090409674269536849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6271346907759131385431597 2351755090409674269536849)
                    ·
                      refine ⟨1763816317807255702152637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2351755090409674269536849 1763816317807255702152637)
                      ·
                        rfl

theorem cell23_3435020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_3435020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435020 prefixEnd_3435020 := by exact prefixLift 3435020
  have htrace : WordTrace (prefixWord ++ tailWord_3435020) baseStart_3435020 baseEnd_3435020 := by
    simpa [prefixWord, tailWord_3435020, baseEnd_3435020] using wordTrace_append hprefix tailTrace_3435020
  have hstable : (prefixWord ++ tailWord_3435020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435020).length < 2 ^ (prefixWord ++ tailWord_3435020).sum := by decide
  have hdescent : baseEnd_3435020 < baseStart_3435020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435029 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_3435029 : Nat := 118140960795 + 3435029 * 2 ^ 59
def prefixEnd_3435029 : Nat := 4983230072969 + 3 ^ 40 * 3435029 * 2
def baseEnd_3435029 : Nat := 1763820939133146166940095

theorem tailTrace_3435029 : CollatzResearch.WordTrace tailWord_3435029 prefixEnd_3435029 1763820939133146166940095 := by
  unfold tailWord_3435029
  simp only [CollatzResearch.WordTrace]
  refine ⟨125285800272484064092220141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83523866848322709394813427 125285800272484064092220141)
  ·
    refine ⟨46982175102181524034582553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125285800272484064092220141 46982175102181524034582553)
    ·
      refine ⟨35236631326636143025936915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46982175102181524034582553 35236631326636143025936915)
      ·
        refine ⟨52854946989954214538905373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35236631326636143025936915 52854946989954214538905373)
        ·
          refine ⟨19820605121232830452089515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52854946989954214538905373 19820605121232830452089515)
          ·
            refine ⟨29730907681849245678134273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19820605121232830452089515 29730907681849245678134273)
            ·
              refine ⟨22298180761386934258600705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29730907681849245678134273 22298180761386934258600705)
              ·
                refine ⟨16723635571040200693950529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22298180761386934258600705 16723635571040200693950529)
                ·
                  refine ⟨12542726678280150520462897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16723635571040200693950529 12542726678280150520462897)
                  ·
                    refine ⟨9407045008710112890347173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12542726678280150520462897 9407045008710112890347173)
                    ·
                      refine ⟨1763820939133146166940095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9407045008710112890347173 1763820939133146166940095)
                      ·
                        rfl

theorem cell23_3435029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_3435029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435029 prefixEnd_3435029 := by exact prefixLift 3435029
  have htrace : WordTrace (prefixWord ++ tailWord_3435029) baseStart_3435029 baseEnd_3435029 := by
    simpa [prefixWord, tailWord_3435029, baseEnd_3435029] using wordTrace_append hprefix tailTrace_3435029
  have hstable : (prefixWord ++ tailWord_3435029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435029).length < 2 ^ (prefixWord ++ tailWord_3435029).sum := by decide
  have hdescent : baseEnd_3435029 < baseStart_3435029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435050 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_3435050 : Nat := 118140960795 + 3435050 * 2 ^ 59
def prefixEnd_3435050 : Nat := 4983230072969 + 3 ^ 40 * 3435050 * 2
def baseEnd_3435050 : Nat := 1763831722226890584777499

theorem tailTrace_3435050 : CollatzResearch.WordTrace tailWord_3435050 prefixEnd_3435050 1763831722226890584777499 := by
  unfold tailWord_3435050
  simp only [CollatzResearch.WordTrace]
  refine ⟨31321641551351996169683651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83524377470271989785823069 31321641551351996169683651)
  ·
    refine ⟨46982462327027994254525477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31321641551351996169683651 46982462327027994254525477)
    ·
      refine ⟨8809211686317748922723527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46982462327027994254525477 8809211686317748922723527)
      ·
        refine ⟨13213817529476623384085291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8809211686317748922723527 13213817529476623384085291)
        ·
          refine ⟨19820726294214935076127937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13213817529476623384085291 19820726294214935076127937)
          ·
            refine ⟨14865544720661201307095953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19820726294214935076127937 14865544720661201307095953)
            ·
              refine ⟨11149158540495900980321965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14865544720661201307095953 11149158540495900980321965)
              ·
                refine ⟨4180934452685962867620737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11149158540495900980321965 4180934452685962867620737)
                ·
                  refine ⟨3135700839514472150715553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4180934452685962867620737 3135700839514472150715553)
                  ·
                    refine ⟨2351775629635854113036665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3135700839514472150715553 2351775629635854113036665)
                    ·
                      refine ⟨1763831722226890584777499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2351775629635854113036665 1763831722226890584777499)
                      ·
                        rfl

theorem cell23_3435050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_3435050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435050 prefixEnd_3435050 := by exact prefixLift 3435050
  have htrace : WordTrace (prefixWord ++ tailWord_3435050) baseStart_3435050 baseEnd_3435050 := by
    simpa [prefixWord, tailWord_3435050, baseEnd_3435050] using wordTrace_append hprefix tailTrace_3435050
  have hstable : (prefixWord ++ tailWord_3435050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435050).length < 2 ^ (prefixWord ++ tailWord_3435050).sum := by decide
  have hdescent : baseEnd_3435050 < baseStart_3435050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435073 : List Nat := [1, 2, 5, 1, 1, 3, 2, 3, 5]
def baseStart_3435073 : Nat := 118140960795 + 3435073 * 2 ^ 59
def prefixEnd_3435073 : Nat := 4983230072969 + 3 ^ 40 * 3435073 * 2
def baseEnd_3435073 : Nat := 195982614697993777198877

theorem tailTrace_3435073 : CollatzResearch.WordTrace tailWord_3435073 prefixEnd_3435073 195982614697993777198877 := by
  unfold tailWord_3435073
  simp only [CollatzResearch.WordTrace]
  refine ⟨125287405084324659606821873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83524936722883106404547915 125287405084324659606821873)
  ·
    refine ⟨93965553813243494705116405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125287405084324659606821873 93965553813243494705116405)
    ·
      refine ⟨8809270669991577628604663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93965553813243494705116405 8809270669991577628604663)
      ·
        refine ⟨13213906004987366442906995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8809270669991577628604663 13213906004987366442906995)
        ·
          refine ⟨19820859007481049664360493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13213906004987366442906995 19820859007481049664360493)
          ·
            refine ⟨7432822127805393624135185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19820859007481049664360493 7432822127805393624135185)
            ·
              refine ⟨5574616595854045218101389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7432822127805393624135185 5574616595854045218101389)
              ·
                refine ⟨2090481223445266956788021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5574616595854045218101389 2090481223445266956788021)
                ·
                  refine ⟨195982614697993777198877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2090481223445266956788021 195982614697993777198877)
                  ·
                    rfl

theorem cell23_3435073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 5].length) (baseStart_3435073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435073 prefixEnd_3435073 := by exact prefixLift 3435073
  have htrace : WordTrace (prefixWord ++ tailWord_3435073) baseStart_3435073 baseEnd_3435073 := by
    simpa [prefixWord, tailWord_3435073, baseEnd_3435073] using wordTrace_append hprefix tailTrace_3435073
  have hstable : (prefixWord ++ tailWord_3435073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435073).length < 2 ^ (prefixWord ++ tailWord_3435073).sum := by decide
  have hdescent : baseEnd_3435073 < baseStart_3435073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435116 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 3, 4]
def baseStart_3435116 : Nat := 118140960795 + 3435116 * 2 ^ 59
def prefixEnd_3435116 : Nat := 4983230072969 + 3 ^ 40 * 3435116 * 2
def baseEnd_3435116 : Nat := 587955203983362442184065

theorem tailTrace_3435116 : CollatzResearch.WordTrace tailWord_3435116 prefixEnd_3435116 587955203983362442184065 := by
  unfold tailWord_3435116
  simp only [CollatzResearch.WordTrace]
  refine ⟨62644486711584438975318601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83525982282112585300424801 62644486711584438975318601)
  ·
    refine ⟨46983365033688329231488951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62644486711584438975318601 46983365033688329231488951)
    ·
      refine ⟨70475047550532493847233427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46983365033688329231488951 70475047550532493847233427)
      ·
        refine ⟨105712571325798740770850141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70475047550532493847233427 105712571325798740770850141)
        ·
          refine ⟨39642214247174527789068803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105712571325798740770850141 39642214247174527789068803)
          ·
            refine ⟨59463321370761791683603205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39642214247174527789068803 59463321370761791683603205)
            ·
              refine ⟨11149372757017835940675601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59463321370761791683603205 11149372757017835940675601)
              ·
                refine ⟨8362029567763376955506701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11149372757017835940675601 8362029567763376955506701)
                ·
                  refine ⟨3135761087911266358315013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8362029567763376955506701 3135761087911266358315013)
                  ·
                    refine ⟨587955203983362442184065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3135761087911266358315013 587955203983362442184065)
                    ·
                      rfl

theorem cell23_3435116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_3435116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435116 prefixEnd_3435116 := by exact prefixLift 3435116
  have htrace : WordTrace (prefixWord ++ tailWord_3435116) baseStart_3435116 baseEnd_3435116 := by
    simpa [prefixWord, tailWord_3435116, baseEnd_3435116] using wordTrace_append hprefix tailTrace_3435116
  have hstable : (prefixWord ++ tailWord_3435116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435116).length < 2 ^ (prefixWord ++ tailWord_3435116).sum := by decide
  have hdescent : baseEnd_3435116 < baseStart_3435116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435129 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 8]
def baseStart_3435129 : Nat := 118140960795 + 3435129 * 2 ^ 59
def prefixEnd_3435129 : Nat := 4983230072969 + 3 ^ 40 * 3435129 * 2
def baseEnd_3435129 : Nat := 195985809688732863965515

theorem tailTrace_3435129 : CollatzResearch.WordTrace tailWord_3435129 prefixEnd_3435129 195985809688732863965515 := by
  unfold tailWord_3435129
  simp only [CollatzResearch.WordTrace]
  refine ⟨125289447572121781170860441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83526298381414520780573627 125289447572121781170860441)
  ·
    refine ⟨93967085679091335878145331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125289447572121781170860441 93967085679091335878145331)
    ·
      refine ⟨140950628518637003817217997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93967085679091335878145331 140950628518637003817217997)
      ·
        refine ⟨52856485694488876431456749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140950628518637003817217997 52856485694488876431456749)
        ·
          refine ⟨19821182135433328661796281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52856485694488876431456749 19821182135433328661796281)
          ·
            refine ⟨14865886601574996496347211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19821182135433328661796281 14865886601574996496347211)
            ·
              refine ⟨22298829902362494744520817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14865886601574996496347211 22298829902362494744520817)
              ·
                refine ⟨16724122426771871058390613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22298829902362494744520817 16724122426771871058390613)
                ·
                  refine ⟨195985809688732863965515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16724122426771871058390613 195985809688732863965515)
                  ·
                    rfl

theorem cell23_3435129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 8].length) (baseStart_3435129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435129 prefixEnd_3435129 := by exact prefixLift 3435129
  have htrace : WordTrace (prefixWord ++ tailWord_3435129) baseStart_3435129 baseEnd_3435129 := by
    simpa [prefixWord, tailWord_3435129, baseEnd_3435129] using wordTrace_append hprefix tailTrace_3435129
  have hstable : (prefixWord ++ tailWord_3435129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435129).length < 2 ^ (prefixWord ++ tailWord_3435129).sum := by decide
  have hdescent : baseEnd_3435129 < baseStart_3435129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435183 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 2, 3, 2]
def baseStart_3435183 : Nat := 118140960795 + 3435183 * 2 ^ 59
def prefixEnd_3435183 : Nat := 4983230072969 + 3 ^ 40 * 3435183 * 2
def baseEnd_3435183 : Nat := 1763900015153938564414387

theorem tailTrace_3435183 : CollatzResearch.WordTrace tailWord_3435183 prefixEnd_3435183 1763900015153938564414387 := by
  unfold tailWord_3435183
  simp only [CollatzResearch.WordTrace]
  refine ⟨125291417113926148393326203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83527611409284098928884135 125291417113926148393326203)
  ·
    refine ⟨187937125670889222589989305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125291417113926148393326203 187937125670889222589989305)
    ·
      refine ⟨140952844253166916942491979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187937125670889222589989305 140952844253166916942491979)
      ·
        refine ⟨211429266379750375413737969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140952844253166916942491979 211429266379750375413737969)
        ·
          refine ⟨158571949784812781560303477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211429266379750375413737969 158571949784812781560303477)
          ·
            refine ⟨14866120292326198271278451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158571949784812781560303477 14866120292326198271278451)
            ·
              refine ⟨22299180438489297406917677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14866120292326198271278451 22299180438489297406917677)
              ·
                refine ⟨8362192664433486527594129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22299180438489297406917677 8362192664433486527594129)
                ·
                  refine ⟨6271644498325114895695597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8362192664433486527594129 6271644498325114895695597)
                  ·
                    refine ⟨2351866686871918085885849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6271644498325114895695597 2351866686871918085885849)
                    ·
                      refine ⟨1763900015153938564414387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2351866686871918085885849 1763900015153938564414387)
                      ·
                        rfl

theorem cell23_3435183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 3, 2].length) (baseStart_3435183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435183 prefixEnd_3435183 := by exact prefixLift 3435183
  have htrace : WordTrace (prefixWord ++ tailWord_3435183) baseStart_3435183 baseEnd_3435183 := by
    simpa [prefixWord, tailWord_3435183, baseEnd_3435183] using wordTrace_append hprefix tailTrace_3435183
  have hstable : (prefixWord ++ tailWord_3435183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435183).length < 2 ^ (prefixWord ++ tailWord_3435183).sum := by decide
  have hdescent : baseEnd_3435183 < baseStart_3435183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435201 : List Nat := [1, 2, 6, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3435201 : Nat := 118140960795 + 3435201 * 2 ^ 59
def prefixEnd_3435201 : Nat := 4983230072969 + 3 ^ 40 * 3435201 * 2
def baseEnd_3435201 : Nat := 587969752601906497996435

theorem tailTrace_3435201 : CollatzResearch.WordTrace tailWord_3435201 prefixEnd_3435201 587969752601906497996435 := by
  unfold tailWord_3435201
  simp only [CollatzResearch.WordTrace]
  refine ⟨125292073627860937467481457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83528049085240624978320971 125292073627860937467481457)
  ·
    refine ⟨93969055220895703100611093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125292073627860937467481457 93969055220895703100611093)
    ·
      refine ⟨4404799463479486082841145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93969055220895703100611093 4404799463479486082841145)
      ·
        refine ⟨3303599597609614562130859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4404799463479486082841145 3303599597609614562130859)
        ·
          refine ⟨4955399396414421843196289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3303599597609614562130859 4955399396414421843196289)
          ·
            refine ⟨3716549547310816382397217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4955399396414421843196289 3716549547310816382397217)
            ·
              refine ⟨2787412160483112286797913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3716549547310816382397217 2787412160483112286797913)
              ·
                refine ⟨2090559120362334215098435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2787412160483112286797913 2090559120362334215098435)
                ·
                  refine ⟨3135838680543501322647653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090559120362334215098435 3135838680543501322647653)
                  ·
                    refine ⟨587969752601906497996435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3135838680543501322647653 587969752601906497996435)
                    ·
                      rfl

theorem cell23_3435201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3435201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435201 prefixEnd_3435201 := by exact prefixLift 3435201
  have htrace : WordTrace (prefixWord ++ tailWord_3435201) baseStart_3435201 baseEnd_3435201 := by
    simpa [prefixWord, tailWord_3435201, baseEnd_3435201] using wordTrace_append hprefix tailTrace_3435201
  have hstable : (prefixWord ++ tailWord_3435201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435201).length < 2 ^ (prefixWord ++ tailWord_3435201).sum := by decide
  have hdescent : baseEnd_3435201 < baseStart_3435201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435223 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 2, 4]
def baseStart_3435223 : Nat := 118140960795 + 3435223 * 2 ^ 59
def prefixEnd_3435223 : Nat := 4983230072969 + 3 ^ 40 * 3435223 * 2
def baseEnd_3435223 : Nat := 587973518126706135971401

theorem tailTrace_3435223 : CollatzResearch.WordTrace tailWord_3435223 prefixEnd_3435223 587973518126706135971401 := by
  unfold tailWord_3435223
  simp only [CollatzResearch.WordTrace]
  refine ⟨125292876033781235224782323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83528584022520823483188215 125292876033781235224782323)
  ·
    refine ⟨187939314050671852837173485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125292876033781235224782323 187939314050671852837173485)
    ·
      refine ⟨70477242769001944813940057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187939314050671852837173485 70477242769001944813940057)
      ·
        refine ⟨52857932076751458610455043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70477242769001944813940057 52857932076751458610455043)
        ·
          refine ⟨79286898115127187915682565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52857932076751458610455043 79286898115127187915682565)
          ·
            refine ⟨14866293396586347734190481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79286898115127187915682565 14866293396586347734190481)
            ·
              refine ⟨11149720047439760800642861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14866293396586347734190481 11149720047439760800642861)
              ·
                refine ⟨4181145017789910300241073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11149720047439760800642861 4181145017789910300241073)
                ·
                  refine ⟨3135858763342432725180805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4181145017789910300241073 3135858763342432725180805)
                  ·
                    refine ⟨587973518126706135971401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3135858763342432725180805 587973518126706135971401)
                    ·
                      rfl

theorem cell23_3435223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_3435223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435223 prefixEnd_3435223 := by exact prefixLift 3435223
  have htrace : WordTrace (prefixWord ++ tailWord_3435223) baseStart_3435223 baseEnd_3435223 := by
    simpa [prefixWord, tailWord_3435223, baseEnd_3435223] using wordTrace_append hprefix tailTrace_3435223
  have hstable : (prefixWord ++ tailWord_3435223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435223).length < 2 ^ (prefixWord ++ tailWord_3435223).sum := by decide
  have hdescent : baseEnd_3435223 < baseStart_3435223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435233 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_3435233 : Nat := 118140960795 + 3435233 * 2 ^ 59
def prefixEnd_3435233 : Nat := 4983230072969 + 3 ^ 40 * 3435233 * 2
def baseEnd_3435233 : Nat := 1763925689186663368789157

theorem tailTrace_3435233 : CollatzResearch.WordTrace tailWord_3435233 prefixEnd_3435233 1763925689186663368789157 := by
  unfold tailWord_3435233
  simp only [CollatzResearch.WordTrace]
  refine ⟨125293240763745006932646353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83528827175830004621764235 125293240763745006932646353)
  ·
    refine ⟨93969930572808755199484765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125293240763745006932646353 93969930572808755199484765)
    ·
      refine ⟨35238723964803283199806787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93969930572808755199484765 35238723964803283199806787)
      ·
        refine ⟨52858085947204924799710181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35238723964803283199806787 52858085947204924799710181)
        ·
          refine ⟨9910891115100923399945659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52858085947204924799710181 9910891115100923399945659)
          ·
            refine ⟨14866336672651385099918489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9910891115100923399945659 14866336672651385099918489)
            ·
              refine ⟨11149752504488538824938867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14866336672651385099918489 11149752504488538824938867)
              ·
                refine ⟨16724628756732808237408301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11149752504488538824938867 16724628756732808237408301)
                ·
                  refine ⟨6271735783774803089028113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16724628756732808237408301 6271735783774803089028113)
                  ·
                    refine ⟨4703801837831102316771085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6271735783774803089028113 4703801837831102316771085)
                    ·
                      refine ⟨1763925689186663368789157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4703801837831102316771085 1763925689186663368789157)
                      ·
                        rfl

theorem cell23_3435233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_3435233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435233 prefixEnd_3435233 := by exact prefixLift 3435233
  have htrace : WordTrace (prefixWord ++ tailWord_3435233) baseStart_3435233 baseEnd_3435233 := by
    simpa [prefixWord, tailWord_3435233, baseEnd_3435233] using wordTrace_append hprefix tailTrace_3435233
  have hstable : (prefixWord ++ tailWord_3435233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435233).length < 2 ^ (prefixWord ++ tailWord_3435233).sum := by decide
  have hdescent : baseEnd_3435233 < baseStart_3435233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435247 : List Nat := [1, 1, 2, 1, 5, 2, 1, 5, 1, 2, 2]
def baseStart_3435247 : Nat := 118140960795 + 3435247 * 2 ^ 59
def prefixEnd_3435247 : Nat := 4983230072969 + 3 ^ 40 * 3435247 * 2
def baseEnd_3435247 : Nat := 1763932877915826314014093

theorem tailTrace_3435247 : CollatzResearch.WordTrace tailWord_3435247 prefixEnd_3435247 1763932877915826314014093 := by
  unfold tailWord_3435247
  simp only [CollatzResearch.WordTrace]
  refine ⟨125293751385694287323655995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83529167590462858215770663 125293751385694287323655995)
  ·
    refine ⟨187940627078541430985483993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125293751385694287323655995 187940627078541430985483993)
    ·
      refine ⟨140955470308906073239112995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187940627078541430985483993 140955470308906073239112995)
      ·
        refine ⟨211433205463359109858669493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140955470308906073239112995 211433205463359109858669493)
        ·
          refine ⟨19821863012189916549250265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211433205463359109858669493 19821863012189916549250265)
          ·
            refine ⟨14866397259142437411937699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19821863012189916549250265 14866397259142437411937699)
            ·
              refine ⟨22299595888713656117906549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14866397259142437411937699 22299595888713656117906549)
              ·
                refine ⟨2090587114566905261053739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22299595888713656117906549 2090587114566905261053739)
                ·
                  refine ⟨3135880671850357891580609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090587114566905261053739 3135880671850357891580609)
                  ·
                    refine ⟨2351910503887768418685457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3135880671850357891580609 2351910503887768418685457)
                    ·
                      refine ⟨1763932877915826314014093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2351910503887768418685457 1763932877915826314014093)
                      ·
                        rfl

theorem cell23_3435247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 1, 2, 2].length) (baseStart_3435247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435247 prefixEnd_3435247 := by exact prefixLift 3435247
  have htrace : WordTrace (prefixWord ++ tailWord_3435247) baseStart_3435247 baseEnd_3435247 := by
    simpa [prefixWord, tailWord_3435247, baseEnd_3435247] using wordTrace_append hprefix tailTrace_3435247
  have hstable : (prefixWord ++ tailWord_3435247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435247).length < 2 ^ (prefixWord ++ tailWord_3435247).sum := by decide
  have hdescent : baseEnd_3435247 < baseStart_3435247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435250 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3435250 : Nat := 118140960795 + 3435250 * 2 ^ 59
def prefixEnd_3435250 : Nat := 4983230072969 + 3 ^ 40 * 3435250 * 2
def baseEnd_3435250 : Nat := 1763934418357789802276579

theorem tailTrace_3435250 : CollatzResearch.WordTrace tailWord_3435250 prefixEnd_3435250 1763934418357789802276579 := by
  unfold tailWord_3435250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31323465201170854709003801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83529240536455612557343469 31323465201170854709003801)
  ·
    refine ⟨23492598900878141031752851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31323465201170854709003801 23492598900878141031752851)
    ·
      refine ⟨35238898351317211547629277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23492598900878141031752851 35238898351317211547629277)
      ·
        refine ⟨13214586881743954330360979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35238898351317211547629277 13214586881743954330360979)
        ·
          refine ⟨19821880322615931495541469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13214586881743954330360979 19821880322615931495541469)
          ·
            refine ⟨7433205120980974310828051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19821880322615931495541469 7433205120980974310828051)
            ·
              refine ⟨11149807681471461466242077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7433205120980974310828051 11149807681471461466242077)
              ·
                refine ⟨4181177880551798049840779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11149807681471461466242077 4181177880551798049840779)
                ·
                  refine ⟨6271766820827697074761169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4181177880551798049840779 6271766820827697074761169)
                  ·
                    refine ⟨4703825115620772806070877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6271766820827697074761169 4703825115620772806070877)
                    ·
                      refine ⟨1763934418357789802276579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4703825115620772806070877 1763934418357789802276579)
                      ·
                        rfl

theorem cell23_3435250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3435250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435250 prefixEnd_3435250 := by exact prefixLift 3435250
  have htrace : WordTrace (prefixWord ++ tailWord_3435250) baseStart_3435250 baseEnd_3435250 := by
    simpa [prefixWord, tailWord_3435250, baseEnd_3435250] using wordTrace_append hprefix tailTrace_3435250
  have hstable : (prefixWord ++ tailWord_3435250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435250).length < 2 ^ (prefixWord ++ tailWord_3435250).sum := by decide
  have hdescent : baseEnd_3435250 < baseStart_3435250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435273 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 5, 3, 2]
def baseStart_3435273 : Nat := 118140960795 + 3435273 * 2 ^ 59
def prefixEnd_3435273 : Nat := 4983230072969 + 3 ^ 40 * 3435273 * 2
def baseEnd_3435273 : Nat := 1763946228412843212288973

theorem tailTrace_3435273 : CollatzResearch.WordTrace tailWord_3435273 prefixEnd_3435273 1763946228412843212288973 := by
  unfold tailWord_3435273
  simp only [CollatzResearch.WordTrace]
  refine ⟨125294699683600093764102473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83529799789066729176068315 125294699683600093764102473)
  ·
    refine ⟨93971024762700070323076855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125294699683600093764102473 93971024762700070323076855)
    ·
      refine ⟨140956537144050105484615283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93971024762700070323076855 140956537144050105484615283)
      ·
        refine ⟨211434805716075158226922925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140956537144050105484615283 211434805716075158226922925)
        ·
          refine ⟨79288052143528184335096097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211434805716075158226922925 79288052143528184335096097)
          ·
            refine ⟨59466039107646138251322073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79288052143528184335096097 59466039107646138251322073)
            ·
              refine ⟨44599529330734603688491555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59466039107646138251322073 44599529330734603688491555)
              ·
                refine ⟨66899293996101905532737333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44599529330734603688491555 66899293996101905532737333)
                ·
                  refine ⟨6271808812134553643694125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66899293996101905532737333 6271808812134553643694125)
                  ·
                    refine ⟨2351928304550457616385297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6271808812134553643694125 2351928304550457616385297)
                    ·
                      refine ⟨1763946228412843212288973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2351928304550457616385297 1763946228412843212288973)
                      ·
                        rfl

theorem cell23_3435273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 3, 2].length) (baseStart_3435273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435273 prefixEnd_3435273 := by exact prefixLift 3435273
  have htrace : WordTrace (prefixWord ++ tailWord_3435273) baseStart_3435273 baseEnd_3435273 := by
    simpa [prefixWord, tailWord_3435273, baseEnd_3435273] using wordTrace_append hprefix tailTrace_3435273
  have hstable : (prefixWord ++ tailWord_3435273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435273).length < 2 ^ (prefixWord ++ tailWord_3435273).sum := by decide
  have hdescent : baseEnd_3435273 < baseStart_3435273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435320 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 4, 2, 2]
def baseStart_3435320 : Nat := 118140960795 + 3435320 * 2 ^ 59
def prefixEnd_3435320 : Nat := 4983230072969 + 3 ^ 40 * 3435320 * 2
def baseEnd_3435320 : Nat := 1763970362003604528401257

theorem tailTrace_3435320 : CollatzResearch.WordTrace tailWord_3435320 prefixEnd_3435320 1763970362003604528401257 := by
  unfold tailWord_3435320
  simp only [CollatzResearch.WordTrace]
  refine ⟨62648206957214910395531707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83530942609619880527375609 62648206957214910395531707)
  ·
    refine ⟨93972310435822365593297561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62648206957214910395531707 93972310435822365593297561)
    ·
      refine ⟨70479232826866774194973171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93972310435822365593297561 70479232826866774194973171)
      ·
        refine ⟨105718849240300161292459757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70479232826866774194973171 105718849240300161292459757)
        ·
          refine ⟨39644568465112560484672409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105718849240300161292459757 39644568465112560484672409)
          ·
            refine ⟨29733426348834420363504307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39644568465112560484672409 29733426348834420363504307)
            ·
              refine ⟨44600139523251630545256461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29733426348834420363504307 44600139523251630545256461)
              ·
                refine ⟨16725052321219361454471173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44600139523251630545256461 16725052321219361454471173)
                ·
                  refine ⟨3135947310228630272713345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16725052321219361454471173 3135947310228630272713345)
                  ·
                    refine ⟨2351960482671472704535009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3135947310228630272713345 2351960482671472704535009)
                    ·
                      refine ⟨1763970362003604528401257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2351960482671472704535009 1763970362003604528401257)
                      ·
                        rfl

theorem cell23_3435320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4, 2, 2].length) (baseStart_3435320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435320 prefixEnd_3435320 := by exact prefixLift 3435320
  have htrace : WordTrace (prefixWord ++ tailWord_3435320) baseStart_3435320 baseEnd_3435320 := by
    simpa [prefixWord, tailWord_3435320, baseEnd_3435320] using wordTrace_append hprefix tailTrace_3435320
  have hstable : (prefixWord ++ tailWord_3435320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435320).length < 2 ^ (prefixWord ++ tailWord_3435320).sum := by decide
  have hdescent : baseEnd_3435320 < baseStart_3435320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435337 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 2, 2, 2]
def baseStart_3435337 : Nat := 118140960795 + 3435337 * 2 ^ 59
def prefixEnd_3435337 : Nat := 4983230072969 + 3 ^ 40 * 3435337 * 2
def baseEnd_3435337 : Nat := 1763979091174730961888679

theorem tailTrace_3435337 : CollatzResearch.WordTrace tailWord_3435337 prefixEnd_3435337 1763979091174730961888679 := by
  unfold tailWord_3435337
  simp only [CollatzResearch.WordTrace]
  refine ⟨125297033955368232694432265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83531355970245488462954843 125297033955368232694432265)
  ·
    refine ⟨93972775466526174520824199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125297033955368232694432265 93972775466526174520824199)
    ·
      refine ⟨140959163199789261781236299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93972775466526174520824199 140959163199789261781236299)
      ·
        refine ⟨211438744799683892671854449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140959163199789261781236299 211438744799683892671854449)
        ·
          refine ⟨158579058599762919503890837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211438744799683892671854449 158579058599762919503890837)
          ·
            refine ⟨7433393371863886851744883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158579058599762919503890837 7433393371863886851744883)
            ·
              refine ⟨11150090057795830277617325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7433393371863886851744883 11150090057795830277617325)
              ·
                refine ⟨4181283771673436354106497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11150090057795830277617325 4181283771673436354106497)
                ·
                  refine ⟨3135962828755077265579873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4181283771673436354106497 3135962828755077265579873)
                  ·
                    refine ⟨2351972121566307949184905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3135962828755077265579873 2351972121566307949184905)
                    ·
                      refine ⟨1763979091174730961888679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2351972121566307949184905 1763979091174730961888679)
                      ·
                        rfl

theorem cell23_3435337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 2, 2].length) (baseStart_3435337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435337 prefixEnd_3435337 := by exact prefixLift 3435337
  have htrace : WordTrace (prefixWord ++ tailWord_3435337) baseStart_3435337 baseEnd_3435337 := by
    simpa [prefixWord, tailWord_3435337, baseEnd_3435337] using wordTrace_append hprefix tailTrace_3435337
  have hstable : (prefixWord ++ tailWord_3435337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435337).length < 2 ^ (prefixWord ++ tailWord_3435337).sum := by decide
  have hdescent : baseEnd_3435337 < baseStart_3435337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435341 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_3435341 : Nat := 118140960795 + 3435341 * 2 ^ 59
def prefixEnd_3435341 : Nat := 4983230072969 + 3 ^ 40 * 3435341 * 2
def baseEnd_3435341 : Nat := 1763981145097348946238661

theorem tailTrace_3435341 : CollatzResearch.WordTrace tailWord_3435341 prefixEnd_3435341 1763981145097348946238661 := by
  unfold tailWord_3435341
  simp only [CollatzResearch.WordTrace]
  refine ⟨125297179847353741377577877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83531453231569160918385251 125297179847353741377577877)
  ·
    refine ⟨5873305305344706627073963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125297179847353741377577877 5873305305344706627073963)
    ·
      refine ⟨8809957958017059940610945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5873305305344706627073963 8809957958017059940610945)
      ·
        refine ⟨6607468468512794955458209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8809957958017059940610945 6607468468512794955458209)
        ·
          refine ⟨4955601351384596216593657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6607468468512794955458209 4955601351384596216593657)
          ·
            refine ⟨3716701013538447162445243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4955601351384596216593657 3716701013538447162445243)
            ·
              refine ⟨5575051520307670743667865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716701013538447162445243 5575051520307670743667865)
              ·
                refine ⟨4181288640230753057750899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5575051520307670743667865 4181288640230753057750899)
                ·
                  refine ⟨6271932960346129586626349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4181288640230753057750899 6271932960346129586626349)
                  ·
                    refine ⟨2351974860129798594984881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6271932960346129586626349 2351974860129798594984881)
                    ·
                      refine ⟨1763981145097348946238661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2351974860129798594984881 1763981145097348946238661)
                      ·
                        rfl

theorem cell23_3435341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_3435341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435341 prefixEnd_3435341 := by exact prefixLift 3435341
  have htrace : WordTrace (prefixWord ++ tailWord_3435341) baseStart_3435341 baseEnd_3435341 := by
    simpa [prefixWord, tailWord_3435341, baseEnd_3435341] using wordTrace_append hprefix tailTrace_3435341
  have hstable : (prefixWord ++ tailWord_3435341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435341).length < 2 ^ (prefixWord ++ tailWord_3435341).sum := by decide
  have hdescent : baseEnd_3435341 < baseStart_3435341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435377 : List Nat := [1, 2, 2, 2, 1, 6, 2, 2, 5]
def baseStart_3435377 : Nat := 118140960795 + 3435377 * 2 ^ 59
def prefixEnd_3435377 : Nat := 4983230072969 + 3 ^ 40 * 3435377 * 2
def baseEnd_3435377 : Nat := 195999958933434533932055

theorem tailTrace_3435377 : CollatzResearch.WordTrace tailWord_3435377 prefixEnd_3435377 195999958933434533932055 := by
  unfold tailWord_3435377
  simp only [CollatzResearch.WordTrace]
  refine ⟨125298492875223319525888385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83532328583482213017258923 125298492875223319525888385)
  ·
    refine ⟨93973869656417489644416289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125298492875223319525888385 93973869656417489644416289)
    ·
      refine ⟨70480402242313117233312217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93973869656417489644416289 70480402242313117233312217)
      ·
        refine ⟨52860301681734837924984163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70480402242313117233312217 52860301681734837924984163)
        ·
          refine ⟨79290452522602256887476245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52860301681734837924984163 79290452522602256887476245)
          ·
            refine ⟨3716739961996980791600449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79290452522602256887476245 3716739961996980791600449)
            ·
              refine ⟨2787554971497735593700337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3716739961996980791600449 2787554971497735593700337)
              ·
                refine ⟨2090666228623301695275253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2787554971497735593700337 2090666228623301695275253)
                ·
                  refine ⟨195999958933434533932055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2090666228623301695275253 195999958933434533932055)
                  ·
                    rfl

theorem cell23_3435377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 5].length) (baseStart_3435377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435377 prefixEnd_3435377 := by exact prefixLift 3435377
  have htrace : WordTrace (prefixWord ++ tailWord_3435377) baseStart_3435377 baseEnd_3435377 := by
    simpa [prefixWord, tailWord_3435377, baseEnd_3435377] using wordTrace_append hprefix tailTrace_3435377
  have hstable : (prefixWord ++ tailWord_3435377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435377).length < 2 ^ (prefixWord ++ tailWord_3435377).sum := by decide
  have hdescent : baseEnd_3435377 < baseStart_3435377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435386 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_3435386 : Nat := 118140960795 + 3435386 * 2 ^ 59
def prefixEnd_3435386 : Nat := 4983230072969 + 3 ^ 40 * 3435386 * 2
def baseEnd_3435386 : Nat := 588001417242267090058651

theorem tailTrace_3435386 : CollatzResearch.WordTrace tailWord_3435386 prefixEnd_3435386 588001417242267090058651 := by
  unfold tailWord_3435386
  simp only [CollatzResearch.WordTrace]
  refine ⟨31324705283047678515741503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83532547421460476041977341 31324705283047678515741503)
  ·
    refine ⟨46987057924571517773612255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31324705283047678515741503 46987057924571517773612255)
    ·
      refine ⟨70480586886857276660418383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46987057924571517773612255 70480586886857276660418383)
      ·
        refine ⟨105720880330285914990627575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70480586886857276660418383 105720880330285914990627575)
        ·
          refine ⟨158581320495428872485941363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105720880330285914990627575 158581320495428872485941363)
          ·
            refine ⟨237871980743143308728912045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158581320495428872485941363 237871980743143308728912045)
            ·
              refine ⟨89201992778678740773342017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237871980743143308728912045 89201992778678740773342017)
              ·
                refine ⟨66901494584009055580006513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89201992778678740773342017 66901494584009055580006513)
                ·
                  refine ⟨50176120938006791685004885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66901494584009055580006513 50176120938006791685004885)
                  ·
                    refine ⟨588001417242267090058651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50176120938006791685004885 588001417242267090058651)
                    ·
                      rfl

theorem cell23_3435386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_3435386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435386 prefixEnd_3435386 := by exact prefixLift 3435386
  have htrace : WordTrace (prefixWord ++ tailWord_3435386) baseStart_3435386 baseEnd_3435386 := by
    simpa [prefixWord, tailWord_3435386, baseEnd_3435386] using wordTrace_append hprefix tailTrace_3435386
  have hstable : (prefixWord ++ tailWord_3435386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435386).length < 2 ^ (prefixWord ++ tailWord_3435386).sum := by decide
  have hdescent : baseEnd_3435386 < baseStart_3435386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435403 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 5, 4]
def baseStart_3435403 : Nat := 118140960795 + 3435403 * 2 ^ 59
def prefixEnd_3435403 : Nat := 4983230072969 + 3 ^ 40 * 3435403 * 2
def baseEnd_3435403 : Nat := 588004326965975901221125

theorem tailTrace_3435403 : CollatzResearch.WordTrace tailWord_3435403 prefixEnd_3435403 588004326965975901221125 := by
  unfold tailWord_3435403
  simp only [CollatzResearch.WordTrace]
  refine ⟨125299441173129125966334863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83532960782086083977556575 125299441173129125966334863)
  ·
    refine ⟨187949161759693688949502295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125299441173129125966334863 187949161759693688949502295)
    ·
      refine ⟨281923742639540533424253443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187949161759693688949502295 281923742639540533424253443)
      ·
        refine ⟨422885613959310800136380165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281923742639540533424253443 422885613959310800136380165)
        ·
          refine ⟨79291052617370775025571281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 422885613959310800136380165 79291052617370775025571281)
          ·
            refine ⟨59468289463028081269178461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79291052617370775025571281 59468289463028081269178461)
            ·
              refine ⟨22300608548635530475941923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59468289463028081269178461 22300608548635530475941923)
              ·
                refine ⟨33450912822953295713912885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22300608548635530475941923 33450912822953295713912885)
                ·
                  refine ⟨3136023077151871473179333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33450912822953295713912885 3136023077151871473179333)
                  ·
                    refine ⟨588004326965975901221125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3136023077151871473179333 588004326965975901221125)
                    ·
                      rfl

theorem cell23_3435403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 4].length) (baseStart_3435403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435403 prefixEnd_3435403 := by exact prefixLift 3435403
  have htrace : WordTrace (prefixWord ++ tailWord_3435403) baseStart_3435403 baseEnd_3435403 := by
    simpa [prefixWord, tailWord_3435403, baseEnd_3435403] using wordTrace_append hprefix tailTrace_3435403
  have hstable : (prefixWord ++ tailWord_3435403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435403).length < 2 ^ (prefixWord ++ tailWord_3435403).sum := by decide
  have hdescent : baseEnd_3435403 < baseStart_3435403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435423 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3435423 : Nat := 118140960795 + 3435423 * 2 ^ 59
def prefixEnd_3435423 : Nat := 4983230072969 + 3 ^ 40 * 3435423 * 2
def baseEnd_3435423 : Nat := 1764023250511017625413283

theorem tailTrace_3435423 : CollatzResearch.WordTrace tailWord_3435423 prefixEnd_3435423 1764023250511017625413283 := by
  unfold tailWord_3435423
  simp only [CollatzResearch.WordTrace]
  refine ⟨125300170633056669382062923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83533447088704446254708615 125300170633056669382062923)
  ·
    refine ⟨187950255949585004073094385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125300170633056669382062923 187950255949585004073094385)
    ·
      refine ⟨140962691962188753054820789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187950255949585004073094385 140962691962188753054820789)
      ·
        refine ⟨13215252371455195598889449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140962691962188753054820789 13215252371455195598889449)
        ·
          refine ⟨9911439278591396699167087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13215252371455195598889449 9911439278591396699167087)
          ·
            refine ⟨14867158917887095048750631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9911439278591396699167087 14867158917887095048750631)
            ·
              refine ⟨22300738376830642573125947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14867158917887095048750631 22300738376830642573125947)
              ·
                refine ⟨33451107565245963859688921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22300738376830642573125947 33451107565245963859688921)
                ·
                  refine ⟨25088330673934472894766691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33451107565245963859688921 25088330673934472894766691)
                  ·
                    refine ⟨37632496010901709342150037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25088330673934472894766691 37632496010901709342150037)
                    ·
                      refine ⟨1764023250511017625413283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37632496010901709342150037 1764023250511017625413283)
                      ·
                        rfl

theorem cell23_3435423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3435423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435423 prefixEnd_3435423 := by exact prefixLift 3435423
  have htrace : WordTrace (prefixWord ++ tailWord_3435423) baseStart_3435423 baseEnd_3435423 := by
    simpa [prefixWord, tailWord_3435423, baseEnd_3435423] using wordTrace_append hprefix tailTrace_3435423
  have hstable : (prefixWord ++ tailWord_3435423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435423).length < 2 ^ (prefixWord ++ tailWord_3435423).sum := by decide
  have hdescent : baseEnd_3435423 < baseStart_3435423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435444 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_3435444 : Nat := 118140960795 + 3435444 * 2 ^ 59
def prefixEnd_3435444 : Nat := 4983230072969 + 3 ^ 40 * 3435444 * 2
def baseEnd_3435444 : Nat := 1764034033604762043250687

theorem tailTrace_3435444 : CollatzResearch.WordTrace tailWord_3435444 prefixEnd_3435444 1764034033604762043250687 := by
  unfold tailWord_3435444
  simp only [CollatzResearch.WordTrace]
  refine ⟨62650468282990294984288693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83533957710653726645718257 62650468282990294984288693)
  ·
    refine ⟨5873481401530340154777065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62650468282990294984288693 5873481401530340154777065)
    ·
      refine ⟨4405111051147755116082799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5873481401530340154777065 4405111051147755116082799)
      ·
        refine ⟨6607666576721632674124199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4405111051147755116082799 6607666576721632674124199)
        ·
          refine ⟨9911499865082449011186299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6607666576721632674124199 9911499865082449011186299)
          ·
            refine ⟨14867249797623673516779449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9911499865082449011186299 14867249797623673516779449)
            ·
              refine ⟨11150437348217755137584587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14867249797623673516779449 11150437348217755137584587)
              ·
                refine ⟨16725656022326632706376881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11150437348217755137584587 16725656022326632706376881)
                ·
                  refine ⟨12544242016744974529782661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16725656022326632706376881 12544242016744974529782661)
                  ·
                    refine ⟨2352045378139682724334249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12544242016744974529782661 2352045378139682724334249)
                    ·
                      refine ⟨1764034033604762043250687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352045378139682724334249 1764034033604762043250687)
                      ·
                        rfl

theorem cell23_3435444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_3435444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435444 prefixEnd_3435444 := by exact prefixLift 3435444
  have htrace : WordTrace (prefixWord ++ tailWord_3435444) baseStart_3435444 baseEnd_3435444 := by
    simpa [prefixWord, tailWord_3435444, baseEnd_3435444] using wordTrace_append hprefix tailTrace_3435444
  have hstable : (prefixWord ++ tailWord_3435444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435444).length < 2 ^ (prefixWord ++ tailWord_3435444).sum := by decide
  have hdescent : baseEnd_3435444 < baseStart_3435444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435450 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 6]
def baseStart_3435450 : Nat := 118140960795 + 3435450 * 2 ^ 59
def prefixEnd_3435450 : Nat := 4983230072969 + 3 ^ 40 * 3435450 * 2
def baseEnd_3435450 : Nat := 196004123832076557752851

theorem tailTrace_3435450 : CollatzResearch.WordTrace tailWord_3435450 prefixEnd_3435450 196004123832076557752851 := by
  unfold tailWord_3435450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31325288850989713248323951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83534103602639235328863869 31325288850989713248323951)
  ·
    refine ⟨46987933276484569872485927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31325288850989713248323951 46987933276484569872485927)
    ·
      refine ⟨70481899914726854808728891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46987933276484569872485927 70481899914726854808728891)
      ·
        refine ⟨105722849872090282213093337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70481899914726854808728891 105722849872090282213093337)
        ·
          refine ⟨79292137404067711659820003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105722849872090282213093337 79292137404067711659820003)
          ·
            refine ⟨118938206106101567489730005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79292137404067711659820003 118938206106101567489730005)
            ·
              refine ⟨2787614205611755488040547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 118938206106101567489730005 2787614205611755488040547)
              ·
                refine ⟨4181421308417633232060821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787614205611755488040547 4181421308417633232060821)
                ·
                  refine ⟨196004123832076557752851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4181421308417633232060821 196004123832076557752851)
                  ·
                    rfl

theorem cell23_3435450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_3435450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435450 prefixEnd_3435450 := by exact prefixLift 3435450
  have htrace : WordTrace (prefixWord ++ tailWord_3435450) baseStart_3435450 baseEnd_3435450 := by
    simpa [prefixWord, tailWord_3435450, baseEnd_3435450] using wordTrace_append hprefix tailTrace_3435450
  have hstable : (prefixWord ++ tailWord_3435450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435450).length < 2 ^ (prefixWord ++ tailWord_3435450).sum := by decide
  have hdescent : baseEnd_3435450 < baseStart_3435450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435463 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 3, 5]
def baseStart_3435463 : Nat := 118140960795 + 3435463 * 2 ^ 59
def prefixEnd_3435463 : Nat := 4983230072969 + 3 ^ 40 * 3435463 * 2
def baseEnd_3435463 : Nat := 588014596579065822971033

theorem tailTrace_3435463 : CollatzResearch.WordTrace tailWord_3435463 prefixEnd_3435463 588014596579065822971033 := by
  unfold tailWord_3435463
  simp only [CollatzResearch.WordTrace]
  refine ⟨125301629552911756213519043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83534419701941170809012695 125301629552911756213519043)
  ·
    refine ⟨187952444329367634320278565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125301629552911756213519043 187952444329367634320278565)
    ·
      refine ⟨35241083311756431435052231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187952444329367634320278565 35241083311756431435052231)
      ·
        refine ⟨52861624967634647152578347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35241083311756431435052231 52861624967634647152578347)
        ·
          refine ⟨79292437451451970728867521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52861624967634647152578347 79292437451451970728867521)
          ·
            refine ⟨59469328088588978046650641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79292437451451970728867521 59469328088588978046650641)
            ·
              refine ⟨44601996066441733534987981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59469328088588978046650641 44601996066441733534987981)
              ·
                refine ⟨16725748524915650075620493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44601996066441733534987981 16725748524915650075620493)
                ·
                  refine ⟨6272155696843368778357685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16725748524915650075620493 6272155696843368778357685)
                  ·
                    refine ⟨588014596579065822971033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6272155696843368778357685 588014596579065822971033)
                    ·
                      rfl

theorem cell23_3435463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_3435463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435463 prefixEnd_3435463 := by exact prefixLift 3435463
  have htrace : WordTrace (prefixWord ++ tailWord_3435463) baseStart_3435463 baseEnd_3435463 := by
    simpa [prefixWord, tailWord_3435463, baseEnd_3435463] using wordTrace_append hprefix tailTrace_3435463
  have hstable : (prefixWord ++ tailWord_3435463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435463).length < 2 ^ (prefixWord ++ tailWord_3435463).sum := by decide
  have hdescent : baseEnd_3435463 < baseStart_3435463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435480 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 1, 5]
def baseStart_3435480 : Nat := 118140960795 + 3435480 * 2 ^ 59
def prefixEnd_3435480 : Nat := 4983230072969 + 3 ^ 40 * 3435480 * 2
def baseEnd_3435480 : Nat := 588017506302774634133507

theorem tailTrace_3435480 : CollatzResearch.WordTrace tailWord_3435480 prefixEnd_3435480 588017506302774634133507 := by
  unfold tailWord_3435480
  simp only [CollatzResearch.WordTrace]
  refine ⟨62651124796925084058443947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83534833062566778744591929 62651124796925084058443947)
  ·
    refine ⟨93976687195387626087665921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62651124796925084058443947 93976687195387626087665921)
    ·
      refine ⟨70482515396540719565749441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93976687195387626087665921 70482515396540719565749441)
      ·
        refine ⟨52861886547405539674312081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70482515396540719565749441 52861886547405539674312081)
        ·
          refine ⟨39646414910554154755734061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52861886547405539674312081 39646414910554154755734061)
          ·
            refine ⟨14867405591457808033400273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39646414910554154755734061 14867405591457808033400273)
            ·
              refine ⟨11150554193593356025050205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14867405591457808033400273 11150554193593356025050205)
              ·
                refine ⟨4181457822597508509393827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11150554193593356025050205 4181457822597508509393827)
                ·
                  refine ⟨6272186733896262764090741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4181457822597508509393827 6272186733896262764090741)
                  ·
                    refine ⟨588017506302774634133507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6272186733896262764090741 588017506302774634133507)
                    ·
                      rfl

theorem cell23_3435480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_3435480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435480 prefixEnd_3435480 := by exact prefixLift 3435480
  have htrace : WordTrace (prefixWord ++ tailWord_3435480) baseStart_3435480 baseEnd_3435480 := by
    simpa [prefixWord, tailWord_3435480, baseEnd_3435480] using wordTrace_append hprefix tailTrace_3435480
  have hstable : (prefixWord ++ tailWord_3435480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435480).length < 2 ^ (prefixWord ++ tailWord_3435480).sum := by decide
  have hdescent : baseEnd_3435480 < baseStart_3435480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435513 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 6]
def baseStart_3435513 : Nat := 118140960795 + 3435513 * 2 ^ 59
def prefixEnd_3435513 : Nat := 4983230072969 + 3 ^ 40 * 3435513 * 2
def baseEnd_3435513 : Nat := 1764069463769922273287869

theorem tailTrace_3435513 : CollatzResearch.WordTrace tailWord_3435513 prefixEnd_3435513 1764069463769922273287869 := by
  unfold tailWord_3435513
  simp only [CollatzResearch.WordTrace]
  refine ⟨125303453202730614752839193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83535635468487076501892795 125303453202730614752839193)
  ·
    refine ⟨93977589902047961064629395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125303453202730614752839193 93977589902047961064629395)
    ·
      refine ⟨140966384853071941596944093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93977589902047961064629395 140966384853071941596944093)
      ·
        refine ⟨52862394319901978098854035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140966384853071941596944093 52862394319901978098854035)
        ·
          refine ⟨79293591479852967148281053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52862394319901978098854035 79293591479852967148281053)
          ·
            refine ⟨29735096804944862680605395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79293591479852967148281053 29735096804944862680605395)
            ·
              refine ⟨44602645207417294020908093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29735096804944862680605395 44602645207417294020908093)
              ·
                refine ⟨16725991952781485257840535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44602645207417294020908093 16725991952781485257840535)
                ·
                  refine ⟨25088987929172227886760803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16725991952781485257840535 25088987929172227886760803)
                  ·
                    refine ⟨37633481893758341830141205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25088987929172227886760803 37633481893758341830141205)
                    ·
                      refine ⟨1764069463769922273287869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37633481893758341830141205 1764069463769922273287869)
                      ·
                        rfl

theorem cell23_3435513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_3435513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435513 prefixEnd_3435513 := by exact prefixLift 3435513
  have htrace : WordTrace (prefixWord ++ tailWord_3435513) baseStart_3435513 baseEnd_3435513 := by
    simpa [prefixWord, tailWord_3435513, baseEnd_3435513] using wordTrace_append hprefix tailTrace_3435513
  have hstable : (prefixWord ++ tailWord_3435513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435513).length < 2 ^ (prefixWord ++ tailWord_3435513).sum := by decide
  have hdescent : baseEnd_3435513 < baseStart_3435513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435517 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 5, 2, 2]
def baseStart_3435517 : Nat := 118140960795 + 3435517 * 2 ^ 59
def prefixEnd_3435517 : Nat := 4983230072969 + 3 ^ 40 * 3435517 * 2
def baseEnd_3435517 : Nat := 1764071517692540257637851

theorem tailTrace_3435517 : CollatzResearch.WordTrace tailWord_3435517 prefixEnd_3435517 1764071517692540257637851 := by
  unfold tailWord_3435517
  simp only [CollatzResearch.WordTrace]
  refine ⟨125303599094716123435984805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83535732729810748957323203 125303599094716123435984805)
  ·
    refine ⟨23494424830259273144247151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125303599094716123435984805 23494424830259273144247151)
    ·
      refine ⟨35241637245388909716370727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23494424830259273144247151 35241637245388909716370727)
      ·
        refine ⟨52862455868083364574556091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35241637245388909716370727 52862455868083364574556091)
        ·
          refine ⟨79293683802125046861834137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52862455868083364574556091 79293683802125046861834137)
          ·
            refine ⟨59470262851593785146375603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79293683802125046861834137 59470262851593785146375603)
            ·
              refine ⟨89205394277390677719563405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59470262851593785146375603 89205394277390677719563405)
              ·
                refine ⟨33452022854021504144836277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89205394277390677719563405 33452022854021504144836277)
                ·
                  refine ⟨3136127142564516013578401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33452022854021504144836277 3136127142564516013578401)
                  ·
                    refine ⟨2352095356923387010183801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3136127142564516013578401 2352095356923387010183801)
                    ·
                      refine ⟨1764071517692540257637851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352095356923387010183801 1764071517692540257637851)
                      ·
                        rfl

theorem cell23_3435517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_3435517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435517 prefixEnd_3435517 := by exact prefixLift 3435517
  have htrace : WordTrace (prefixWord ++ tailWord_3435517) baseStart_3435517 baseEnd_3435517 := by
    simpa [prefixWord, tailWord_3435517, baseEnd_3435517] using wordTrace_append hprefix tailTrace_3435517
  have hstable : (prefixWord ++ tailWord_3435517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435517).length < 2 ^ (prefixWord ++ tailWord_3435517).sum := by decide
  have hdescent : baseEnd_3435517 < baseStart_3435517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435530 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_3435530 : Nat := 118140960795 + 3435530 * 2 ^ 59
def prefixEnd_3435530 : Nat := 4983230072969 + 3 ^ 40 * 3435530 * 2
def baseEnd_3435530 : Nat := 1764078192941048706775291

theorem tailTrace_3435530 : CollatzResearch.WordTrace tailWord_3435530 prefixEnd_3435530 1764078192941048706775291 := by
  unfold tailWord_3435530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31326018310917256664052011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83536048829112684437472029 31326018310917256664052011)
  ·
    refine ⟨46989027466375884996078017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31326018310917256664052011 46989027466375884996078017)
    ·
      refine ⟨35241770599781913747058513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46989027466375884996078017 35241770599781913747058513)
      ·
        refine ⟨26431327949836435310293885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35241770599781913747058513 26431327949836435310293885)
        ·
          refine ⟨9911747981188663241360207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26431327949836435310293885 9911747981188663241360207)
          ·
            refine ⟨14867621971782994862040311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9911747981188663241360207 14867621971782994862040311)
            ·
              refine ⟨22301432957674492293060467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14867621971782994862040311 22301432957674492293060467)
              ·
                refine ⟨33452149436511738439590701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22301432957674492293060467 33452149436511738439590701)
                ·
                  refine ⟨12544556038691901914846513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33452149436511738439590701 12544556038691901914846513)
                  ·
                    refine ⟨9408417029018926436134885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12544556038691901914846513 9408417029018926436134885)
                    ·
                      refine ⟨1764078192941048706775291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9408417029018926436134885 1764078192941048706775291)
                      ·
                        rfl

theorem cell23_3435530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_3435530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435530 prefixEnd_3435530 := by exact prefixLift 3435530
  have htrace : WordTrace (prefixWord ++ tailWord_3435530) baseStart_3435530 baseEnd_3435530 := by
    simpa [prefixWord, tailWord_3435530, baseEnd_3435530] using wordTrace_append hprefix tailTrace_3435530
  have hstable : (prefixWord ++ tailWord_3435530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435530).length < 2 ^ (prefixWord ++ tailWord_3435530).sum := by decide
  have hdescent : baseEnd_3435530 < baseStart_3435530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435534 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4]
def baseStart_3435534 : Nat := 118140960795 + 3435534 * 2 ^ 59
def prefixEnd_3435534 : Nat := 4983230072969 + 3 ^ 40 * 3435534 * 2
def baseEnd_3435534 : Nat := 1764080246863666691125273

theorem tailTrace_3435534 : CollatzResearch.WordTrace tailWord_3435534 prefixEnd_3435534 1764080246863666691125273 := by
  unfold tailWord_3435534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15663027391956816917419207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83536146090436356892902437 15663027391956816917419207)
  ·
    refine ⟨23494541087935225376128811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15663027391956816917419207 23494541087935225376128811)
    ·
      refine ⟨35241811631902838064193217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23494541087935225376128811 35241811631902838064193217)
      ·
        refine ⟨26431358723927128548144913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35241811631902838064193217 26431358723927128548144913)
        ·
          refine ⟨19823519042945346411108685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26431358723927128548144913 19823519042945346411108685)
          ·
            refine ⟨7433819641104504904165757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19823519042945346411108685 7433819641104504904165757)
            ·
              refine ⟨2787682365414189339062159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7433819641104504904165757 2787682365414189339062159)
              ·
                refine ⟨4181523548121284008593239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787682365414189339062159 4181523548121284008593239)
                ·
                  refine ⟨6272285322181926012889859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4181523548121284008593239 6272285322181926012889859)
                  ·
                    refine ⟨9408427983272889019334789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6272285322181926012889859 9408427983272889019334789)
                    ·
                      refine ⟨1764080246863666691125273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9408427983272889019334789 1764080246863666691125273)
                      ·
                        rfl

theorem cell23_3435534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_3435534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435534 prefixEnd_3435534 := by exact prefixLift 3435534
  have htrace : WordTrace (prefixWord ++ tailWord_3435534) baseStart_3435534 baseEnd_3435534 := by
    simpa [prefixWord, tailWord_3435534, baseEnd_3435534] using wordTrace_append hprefix tailTrace_3435534
  have hstable : (prefixWord ++ tailWord_3435534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435534).length < 2 ^ (prefixWord ++ tailWord_3435534).sum := by decide
  have hdescent : baseEnd_3435534 < baseStart_3435534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435551 : List Nat := [1, 1, 2, 4, 1, 4, 1, 4, 1, 2, 2]
def baseStart_3435551 : Nat := 118140960795 + 3435551 * 2 ^ 59
def prefixEnd_3435551 : Nat := 4983230072969 + 3 ^ 40 * 3435551 * 2
def baseEnd_3435551 : Nat := 1764088976034793124612695

theorem tailTrace_3435551 : CollatzResearch.WordTrace tailWord_3435551 prefixEnd_3435551 1764088976034793124612695 := by
  unfold tailWord_3435551
  simp only [CollatzResearch.WordTrace]
  refine ⟨125304839176592947242722507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83536559451061964828481671 125304839176592947242722507)
  ·
    refine ⟨187957258764889420864083761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125304839176592947242722507 187957258764889420864083761)
    ·
      refine ⟨140967944073667065648062821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187957258764889420864083761 140967944073667065648062821)
      ·
        refine ⟨26431489513812574809011779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140967944073667065648062821 26431489513812574809011779)
        ·
          refine ⟨39647234270718862213517669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26431489513812574809011779 39647234270718862213517669)
          ·
            refine ⟨7433856425759786665034563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39647234270718862213517669 7433856425759786665034563)
            ·
              refine ⟨11150784638639679997551845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7433856425759786665034563 11150784638639679997551845)
              ·
                refine ⟨2090772119744939999540971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11150784638639679997551845 2090772119744939999540971)
                ·
                  refine ⟨3136158179617409999311457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090772119744939999540971 3136158179617409999311457)
                  ·
                    refine ⟨2352118634713057499483593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3136158179617409999311457 2352118634713057499483593)
                    ·
                      refine ⟨1764088976034793124612695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352118634713057499483593 1764088976034793124612695)
                      ·
                        rfl

theorem cell23_3435551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_3435551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435551 prefixEnd_3435551 := by exact prefixLift 3435551
  have htrace : WordTrace (prefixWord ++ tailWord_3435551) baseStart_3435551 baseEnd_3435551 := by
    simpa [prefixWord, tailWord_3435551, baseEnd_3435551] using wordTrace_append hprefix tailTrace_3435551
  have hstable : (prefixWord ++ tailWord_3435551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435551).length < 2 ^ (prefixWord ++ tailWord_3435551).sum := by decide
  have hdescent : baseEnd_3435551 < baseStart_3435551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435583 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 3, 8]
def baseStart_3435583 : Nat := 118140960795 + 3435583 * 2 ^ 59
def prefixEnd_3435583 : Nat := 4983230072969 + 3 ^ 40 * 3435583 * 2
def baseEnd_3435583 : Nat := 588035135805245666470849

theorem tailTrace_3435583 : CollatzResearch.WordTrace tailWord_3435583 prefixEnd_3435583 588035135805245666470849 := by
  unfold tailWord_3435583
  simp only [CollatzResearch.WordTrace]
  refine ⟨125306006312477016707887403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83537337541651344471924935 125306006312477016707887403)
  ·
    refine ⟨187959009468715525061831105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125306006312477016707887403 187959009468715525061831105)
    ·
      refine ⟨140969257101536643796373329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187959009468715525061831105 140969257101536643796373329)
      ·
        refine ⟨105726942826152482847279997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140969257101536643796373329 105726942826152482847279997)
        ·
          refine ⟨39647603559807181067729999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105726942826152482847279997 39647603559807181067729999)
          ·
            refine ⟨59471405339710771601594999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39647603559807181067729999 59471405339710771601594999)
            ·
              refine ⟨89207108009566157402392499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59471405339710771601594999 89207108009566157402392499)
              ·
                refine ⟨133810662014349236103588749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89207108009566157402392499 133810662014349236103588749)
                ·
                  refine ⟨50178998255380963538845781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133810662014349236103588749 50178998255380963538845781)
                  ·
                    refine ⟨588035135805245666470849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50178998255380963538845781 588035135805245666470849)
                    ·
                      rfl

theorem cell23_3435583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_3435583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435583 prefixEnd_3435583 := by exact prefixLift 3435583
  have htrace : WordTrace (prefixWord ++ tailWord_3435583) baseStart_3435583 baseEnd_3435583 := by
    simpa [prefixWord, tailWord_3435583, baseEnd_3435583] using wordTrace_append hprefix tailTrace_3435583
  have hstable : (prefixWord ++ tailWord_3435583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435583).length < 2 ^ (prefixWord ++ tailWord_3435583).sum := by decide
  have hdescent : baseEnd_3435583 < baseStart_3435583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435603 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 6]
def baseStart_3435603 : Nat := 118140960795 + 3435603 * 2 ^ 59
def prefixEnd_3435603 : Nat := 4983230072969 + 3 ^ 40 * 3435603 * 2
def baseEnd_3435603 : Nat := 1764115677028826921162455

theorem tailTrace_3435603 : CollatzResearch.WordTrace tailWord_3435603 prefixEnd_3435603 1764115677028826921162455 := by
  unfold tailWord_3435603
  simp only [CollatzResearch.WordTrace]
  refine ⟨125306735772404560123615463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83537823848269706749076975 125306735772404560123615463)
  ·
    refine ⟨187960103658606840185423195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125306735772404560123615463 187960103658606840185423195)
    ·
      refine ⟨281940155487910260278134793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187960103658606840185423195 281940155487910260278134793)
      ·
        refine ⟨211455116615932695208601095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281940155487910260278134793 211455116615932695208601095)
        ·
          refine ⟨317182674923899042812901643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211455116615932695208601095 317182674923899042812901643)
          ·
            refine ⟨475774012385848564219352465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317182674923899042812901643 475774012385848564219352465)
            ·
              refine ⟨356830509289386423164514349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475774012385848564219352465 356830509289386423164514349)
              ·
                refine ⟨133811440983519908686692881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 356830509289386423164514349 133811440983519908686692881)
                ·
                  refine ⟨100358580737639931515019661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133811440983519908686692881 100358580737639931515019661)
                  ·
                    refine ⟨37634467776614974318132373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100358580737639931515019661 37634467776614974318132373)
                    ·
                      refine ⟨1764115677028826921162455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37634467776614974318132373 1764115677028826921162455)
                      ·
                        rfl

theorem cell23_3435603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_3435603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435603 prefixEnd_3435603 := by exact prefixLift 3435603
  have htrace : WordTrace (prefixWord ++ tailWord_3435603) baseStart_3435603 baseEnd_3435603 := by
    simpa [prefixWord, tailWord_3435603, baseEnd_3435603] using wordTrace_append hprefix tailTrace_3435603
  have hstable : (prefixWord ++ tailWord_3435603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435603).length < 2 ^ (prefixWord ++ tailWord_3435603).sum := by decide
  have hdescent : baseEnd_3435603 < baseStart_3435603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435610 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3]
def baseStart_3435610 : Nat := 118140960795 + 3435610 * 2 ^ 59
def prefixEnd_3435610 : Nat := 4983230072969 + 3 ^ 40 * 3435610 * 2
def baseEnd_3435610 : Nat := 1764119271393408393774923

theorem tailTrace_3435610 : CollatzResearch.WordTrace tailWord_3435610 prefixEnd_3435610 1764119271393408393774923 := by
  unfold tailWord_3435610
  simp only [CollatzResearch.WordTrace]
  refine ⟨31326747770844800079780071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83537994055586133546080189 31326747770844800079780071)
  ·
    refine ⟨46990121656267200119670107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31326747770844800079780071 46990121656267200119670107)
    ·
      refine ⟨70485182484400800179505161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46990121656267200119670107 70485182484400800179505161)
      ·
        refine ⟨52863886863300600134628871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70485182484400800179505161 52863886863300600134628871)
        ·
          refine ⟨79295830294950900201943307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52863886863300600134628871 79295830294950900201943307)
          ·
            refine ⟨118943745442426350302914961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79295830294950900201943307 118943745442426350302914961)
            ·
              refine ⟨89207809081819762727186221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118943745442426350302914961 89207809081819762727186221)
              ·
                refine ⟨33452928405682411022694833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89207809081819762727186221 33452928405682411022694833)
                ·
                  refine ⟨25089696304261808267021125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33452928405682411022694833 25089696304261808267021125)
                  ·
                    refine ⟨4704318057049089050066461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25089696304261808267021125 4704318057049089050066461)
                    ·
                      refine ⟨1764119271393408393774923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4704318057049089050066461 1764119271393408393774923)
                      ·
                        rfl

theorem cell23_3435610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_3435610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435610 prefixEnd_3435610 := by exact prefixLift 3435610
  have htrace : WordTrace (prefixWord ++ tailWord_3435610) baseStart_3435610 baseEnd_3435610 := by
    simpa [prefixWord, tailWord_3435610, baseEnd_3435610] using wordTrace_append hprefix tailTrace_3435610
  have hstable : (prefixWord ++ tailWord_3435610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435610).length < 2 ^ (prefixWord ++ tailWord_3435610).sum := by decide
  have hdescent : baseEnd_3435610 < baseStart_3435610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435618 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_3435618 : Nat := 118140960795 + 3435618 * 2 ^ 59
def prefixEnd_3435618 : Nat := 4983230072969 + 3 ^ 40 * 3435618 * 2
def baseEnd_3435618 : Nat := 1764123379238644362474887

theorem tailTrace_3435618 : CollatzResearch.WordTrace tailWord_3435618 prefixEnd_3435618 1764123379238644362474887 := by
  unfold tailWord_3435618
  simp only [CollatzResearch.WordTrace]
  refine ⟨31326820716837554421352877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83538188578233478456941005 31326820716837554421352877)
  ·
    refine ⟨11747557768814082908007329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31326820716837554421352877 11747557768814082908007329)
    ·
      refine ⟨8810668326610562181005497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11747557768814082908007329 8810668326610562181005497)
      ·
        refine ⟨6608001244957921635754123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8810668326610562181005497 6608001244957921635754123)
        ·
          refine ⟨9912001867436882453631185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6608001244957921635754123 9912001867436882453631185)
          ·
            refine ⟨7434001400577661840223389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9912001867436882453631185 7434001400577661840223389)
            ·
              refine ⟨2787750525216623190083771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7434001400577661840223389 2787750525216623190083771)
              ·
                refine ⟨4181625787824934785125657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787750525216623190083771 4181625787824934785125657)
                ·
                  refine ⟨3136219340868701088844243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4181625787824934785125657 3136219340868701088844243)
                  ·
                    refine ⟨4704329011303051633266365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3136219340868701088844243 4704329011303051633266365)
                    ·
                      refine ⟨1764123379238644362474887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4704329011303051633266365 1764123379238644362474887)
                      ·
                        rfl

theorem cell23_3435618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_3435618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435618 prefixEnd_3435618 := by exact prefixLift 3435618
  have htrace : WordTrace (prefixWord ++ tailWord_3435618) baseStart_3435618 baseEnd_3435618 := by
    simpa [prefixWord, tailWord_3435618, baseEnd_3435618] using wordTrace_append hprefix tailTrace_3435618
  have hstable : (prefixWord ++ tailWord_3435618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435618).length < 2 ^ (prefixWord ++ tailWord_3435618).sum := by decide
  have hdescent : baseEnd_3435618 < baseStart_3435618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435640 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 1, 5, 3]
def baseStart_3435640 : Nat := 118140960795 + 3435640 * 2 ^ 59
def prefixEnd_3435640 : Nat := 4983230072969 + 3 ^ 40 * 3435640 * 2
def baseEnd_3435640 : Nat := 1764134675813043276399785

theorem tailTrace_3435640 : CollatzResearch.WordTrace tailWord_3435640 prefixEnd_3435640 1764134675813043276399785 := by
  unfold tailWord_3435640
  simp only [CollatzResearch.WordTrace]
  refine ⟨62654042636635257721356187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83538723515513676961808249 62654042636635257721356187)
  ·
    refine ⟨93981063954952886582034281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62654042636635257721356187 93981063954952886582034281)
    ·
      refine ⟨70485797966214664936525711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93981063954952886582034281 70485797966214664936525711)
      ·
        refine ⟨105728696949321997404788567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70485797966214664936525711 105728696949321997404788567)
        ·
          refine ⟨158593045423982996107182851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105728696949321997404788567 158593045423982996107182851)
          ·
            refine ⟨237889568135974494160774277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158593045423982996107182851 237889568135974494160774277)
            ·
              refine ⟨44604294025495217655145177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237889568135974494160774277 44604294025495217655145177)
              ·
                refine ⟨33453220519121413241358883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44604294025495217655145177 33453220519121413241358883)
                ·
                  refine ⟨50179830778682119862038325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33453220519121413241358883 50179830778682119862038325)
                  ·
                    refine ⟨4704359135501448737066093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50179830778682119862038325 4704359135501448737066093)
                    ·
                      refine ⟨1764134675813043276399785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4704359135501448737066093 1764134675813043276399785)
                      ·
                        rfl

theorem cell23_3435640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_3435640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435640 prefixEnd_3435640 := by exact prefixLift 3435640
  have htrace : WordTrace (prefixWord ++ tailWord_3435640) baseStart_3435640 baseEnd_3435640 := by
    simpa [prefixWord, tailWord_3435640, baseEnd_3435640] using wordTrace_append hprefix tailTrace_3435640
  have hstable : (prefixWord ++ tailWord_3435640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435640).length < 2 ^ (prefixWord ++ tailWord_3435640).sum := by decide
  have hdescent : baseEnd_3435640 < baseStart_3435640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435720 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 8]
def baseStart_3435720 : Nat := 118140960795 + 3435720 * 2 ^ 59
def prefixEnd_3435720 : Nat := 4983230072969 + 3 ^ 40 * 3435720 * 2
def baseEnd_3435720 : Nat := 196019528251711440377713

theorem tailTrace_3435720 : CollatzResearch.WordTrace tailWord_3435720 prefixEnd_3435720 196019528251711440377713 := by
  unfold tailWord_3435720
  simp only [CollatzResearch.WordTrace]
  refine ⟨62655501556490344552812307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83540668741987126070416409 62655501556490344552812307)
  ·
    refine ⟨93983252334735516829218461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62655501556490344552812307 93983252334735516829218461)
    ·
      refine ⟨35243719625525818810956923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93983252334735516829218461 35243719625525818810956923)
      ·
        refine ⟨52865579438288728216435385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35243719625525818810956923 52865579438288728216435385)
        ·
          refine ⟨39649184578716546162326539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52865579438288728216435385 39649184578716546162326539)
          ·
            refine ⟨59473776868074819243489809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39649184578716546162326539 59473776868074819243489809)
            ·
              refine ⟨44605332651056114432617357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59473776868074819243489809 44605332651056114432617357)
              ·
                refine ⟨16726999744146042912231509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44605332651056114432617357 16726999744146042912231509)
                ·
                  refine ⟨196019528251711440377713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16726999744146042912231509 196019528251711440377713)
                  ·
                    rfl

theorem cell23_3435720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 8].length) (baseStart_3435720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435720 prefixEnd_3435720 := by exact prefixLift 3435720
  have htrace : WordTrace (prefixWord ++ tailWord_3435720) baseStart_3435720 baseEnd_3435720 := by
    simpa [prefixWord, tailWord_3435720, baseEnd_3435720] using wordTrace_append hprefix tailTrace_3435720
  have hstable : (prefixWord ++ tailWord_3435720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435720).length < 2 ^ (prefixWord ++ tailWord_3435720).sum := by decide
  have hdescent : baseEnd_3435720 < baseStart_3435720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435741 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_3435741 : Nat := 118140960795 + 3435741 * 2 ^ 59
def prefixEnd_3435741 : Nat := 4983230072969 + 3 ^ 40 * 3435741 * 2
def baseEnd_3435741 : Nat := 588062179119715793745607

theorem tailTrace_3435741 : CollatzResearch.WordTrace tailWord_3435741 prefixEnd_3435741 588062179119715793745607 := by
  unfold tailWord_3435741
  simp only [CollatzResearch.WordTrace]
  refine ⟨125311769045904609692139077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83541179363936406461426051 125311769045904609692139077)
  ·
    refine ⟨23495956696107114317276077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125311769045904609692139077 23495956696107114317276077)
    ·
      refine ⟨8810983761040167868978529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23495956696107114317276077 8810983761040167868978529)
      ·
        refine ⟨6608237820780125901733897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8810983761040167868978529 6608237820780125901733897)
        ·
          refine ⟨4956178365585094426300423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6608237820780125901733897 4956178365585094426300423)
          ·
            refine ⟨7434267548377641639450635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4956178365585094426300423 7434267548377641639450635)
            ·
              refine ⟨11151401322566462459175953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7434267548377641639450635 11151401322566462459175953)
              ·
                refine ⟨8363550991924846844381965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11151401322566462459175953 8363550991924846844381965)
                ·
                  refine ⟨3136331621971817566643237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8363550991924846844381965 3136331621971817566643237)
                  ·
                    refine ⟨588062179119715793745607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3136331621971817566643237 588062179119715793745607)
                    ·
                      rfl

theorem cell23_3435741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_3435741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435741 prefixEnd_3435741 := by exact prefixLift 3435741
  have htrace : WordTrace (prefixWord ++ tailWord_3435741) baseStart_3435741 baseEnd_3435741 := by
    simpa [prefixWord, tailWord_3435741, baseEnd_3435741] using wordTrace_append hprefix tailTrace_3435741
  have hstable : (prefixWord ++ tailWord_3435741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435741).length < 2 ^ (prefixWord ++ tailWord_3435741).sum := by decide
  have hdescent : baseEnd_3435741 < baseStart_3435741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435760 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_3435760 : Nat := 118140960795 + 3435760 * 2 ^ 59
def prefixEnd_3435760 : Nat := 4983230072969 + 3 ^ 40 * 3435760 * 2
def baseEnd_3435760 : Nat := 1764196293491582806899233

theorem tailTrace_3435760 : CollatzResearch.WordTrace tailWord_3435760 prefixEnd_3435760 1764196293491582806899233 := by
  unfold tailWord_3435760
  simp only [CollatzResearch.WordTrace]
  refine ⟨62656231016417887968540367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83541641355223850624720489 62656231016417887968540367)
  ·
    refine ⟨93984346524626831952810551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62656231016417887968540367 93984346524626831952810551)
    ·
      refine ⟨140976519786940247929215827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93984346524626831952810551 140976519786940247929215827)
      ·
        refine ⟨211464779680410371893823741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140976519786940247929215827 211464779680410371893823741)
        ·
          refine ⟨79299292380153889460183903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211464779680410371893823741 79299292380153889460183903)
          ·
            refine ⟨118948938570230834190275855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79299292380153889460183903 118948938570230834190275855)
            ·
              refine ⟨178423407855346251285413783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118948938570230834190275855 178423407855346251285413783)
              ·
                refine ⟨267635111783019376928120675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178423407855346251285413783 267635111783019376928120675)
                ·
                  refine ⟨401452667674529065392181013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267635111783019376928120675 401452667674529065392181013)
                  ·
                    refine ⟨18818093797243549940258485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 401452667674529065392181013 18818093797243549940258485)
                    ·
                      refine ⟨1764196293491582806899233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18818093797243549940258485 1764196293491582806899233)
                      ·
                        rfl

theorem cell23_3435760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_3435760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435760 prefixEnd_3435760 := by exact prefixLift 3435760
  have htrace : WordTrace (prefixWord ++ tailWord_3435760) baseStart_3435760 baseEnd_3435760 := by
    simpa [prefixWord, tailWord_3435760, baseEnd_3435760] using wordTrace_append hprefix tailTrace_3435760
  have hstable : (prefixWord ++ tailWord_3435760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435760).length < 2 ^ (prefixWord ++ tailWord_3435760).sum := by decide
  have hdescent : baseEnd_3435760 < baseStart_3435760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435767 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 1, 5]
def baseStart_3435767 : Nat := 118140960795 + 3435767 * 2 ^ 59
def prefixEnd_3435767 : Nat := 4983230072969 + 3 ^ 40 * 3435767 * 2
def baseEnd_3435767 : Nat := 588066629285388093170567

theorem tailTrace_3435767 : CollatzResearch.WordTrace tailWord_3435767 prefixEnd_3435767 588066629285388093170567 := by
  unfold tailWord_3435767
  simp only [CollatzResearch.WordTrace]
  refine ⟨125312717343810416132585555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83541811562540277421723703 125312717343810416132585555)
  ·
    refine ⟨187969076015715624198878333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125312717343810416132585555 187969076015715624198878333)
    ·
      refine ⟨70488403505893359074579375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187969076015715624198878333 70488403505893359074579375)
      ·
        refine ⟨105732605258840038611869063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70488403505893359074579375 105732605258840038611869063)
        ·
          refine ⟨158598907888260057917803595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105732605258840038611869063 158598907888260057917803595)
          ·
            refine ⟨237898361832390086876705393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158598907888260057917803595 237898361832390086876705393)
            ·
              refine ⟨178423771374292565157529045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237898361832390086876705393 178423771374292565157529045)
              ·
                refine ⟨4181807141584981995879587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 178423771374292565157529045 4181807141584981995879587)
                ·
                  refine ⟨6272710712377472993819381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4181807141584981995879587 6272710712377472993819381)
                  ·
                    refine ⟨588066629285388093170567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6272710712377472993819381 588066629285388093170567)
                    ·
                      rfl

theorem cell23_3435767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_3435767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435767 prefixEnd_3435767 := by exact prefixLift 3435767
  have htrace : WordTrace (prefixWord ++ tailWord_3435767) baseStart_3435767 baseEnd_3435767 := by
    simpa [prefixWord, tailWord_3435767, baseEnd_3435767] using wordTrace_append hprefix tailTrace_3435767
  have hstable : (prefixWord ++ tailWord_3435767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435767).length < 2 ^ (prefixWord ++ tailWord_3435767).sum := by decide
  have hdescent : baseEnd_3435767 < baseStart_3435767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435781 : List Nat := [1, 3, 1, 1, 2, 1, 3, 6, 1, 1, 3]
def baseStart_3435781 : Nat := 118140960795 + 3435781 * 2 ^ 59
def prefixEnd_3435781 : Nat := 4983230072969 + 3 ^ 40 * 3435781 * 2
def baseEnd_3435781 : Nat := 1764207076585327224736637

theorem tailTrace_3435781 : CollatzResearch.WordTrace tailWord_3435781 prefixEnd_3435781 1764207076585327224736637 := by
  unfold tailWord_3435781
  simp only [CollatzResearch.WordTrace]
  refine ⟨125313227965759696523595197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83542151977173131015730131 125313227965759696523595197)
  ·
    refine ⟨46992460487159886196348199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125313227965759696523595197 46992460487159886196348199)
    ·
      refine ⟨70488690730739829294522299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46992460487159886196348199 70488690730739829294522299)
      ·
        refine ⟨105733036096109743941783449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70488690730739829294522299 105733036096109743941783449)
        ·
          refine ⟨79299777072082307956337587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105733036096109743941783449 79299777072082307956337587)
          ·
            refine ⟨118949665608123461934506381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79299777072082307956337587 118949665608123461934506381)
            ·
              refine ⟨44606124603046298225439893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118949665608123461934506381 44606124603046298225439893)
              ·
                refine ⟨2090912090767795229317495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44606124603046298225439893 2090912090767795229317495)
                ·
                  refine ⟨3136368136151692843976243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090912090767795229317495 3136368136151692843976243)
                  ·
                    refine ⟨4704552204227539265964365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3136368136151692843976243 4704552204227539265964365)
                    ·
                      refine ⟨1764207076585327224736637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4704552204227539265964365 1764207076585327224736637)
                      ·
                        rfl

theorem cell23_3435781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 1, 1, 3].length) (baseStart_3435781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435781 prefixEnd_3435781 := by exact prefixLift 3435781
  have htrace : WordTrace (prefixWord ++ tailWord_3435781) baseStart_3435781 baseEnd_3435781 := by
    simpa [prefixWord, tailWord_3435781, baseEnd_3435781] using wordTrace_append hprefix tailTrace_3435781
  have hstable : (prefixWord ++ tailWord_3435781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435781).length < 2 ^ (prefixWord ++ tailWord_3435781).sum := by decide
  have hdescent : baseEnd_3435781 < baseStart_3435781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435804 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_3435804 : Nat := 118140960795 + 3435804 * 2 ^ 59
def prefixEnd_3435804 : Nat := 4983230072969 + 3 ^ 40 * 3435804 * 2
def baseEnd_3435804 : Nat := 1764218886640380634749031

theorem tailTrace_3435804 : CollatzResearch.WordTrace tailWord_3435804 prefixEnd_3435804 1764218886640380634749031 := by
  unfold tailWord_3435804
  simp only [CollatzResearch.WordTrace]
  refine ⟨62657033422338185725841233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83542711229784247634454977 62657033422338185725841233)
  ·
    refine ⟨46992775066753639294380925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62657033422338185725841233 46992775066753639294380925)
    ·
      refine ⟨17622290650032614735392847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46992775066753639294380925 17622290650032614735392847)
      ·
        refine ⟨26433435975048922103089271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17622290650032614735392847 26433435975048922103089271)
        ·
          refine ⟨39650153962573383154633907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26433435975048922103089271 39650153962573383154633907)
          ·
            refine ⟨59475230943860074731950861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39650153962573383154633907 59475230943860074731950861)
            ·
              refine ⟨22303211603947528024481573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59475230943860074731950861 22303211603947528024481573)
              ·
                refine ⟨4181852175740161504590295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22303211603947528024481573 4181852175740161504590295)
                ·
                  refine ⟨6272778263610242256885443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4181852175740161504590295 6272778263610242256885443)
                  ·
                    refine ⟨9409167395415363385328165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6272778263610242256885443 9409167395415363385328165)
                    ·
                      refine ⟨1764218886640380634749031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9409167395415363385328165 1764218886640380634749031)
                      ·
                        rfl

theorem cell23_3435804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_3435804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435804 prefixEnd_3435804 := by exact prefixLift 3435804
  have htrace : WordTrace (prefixWord ++ tailWord_3435804) baseStart_3435804 baseEnd_3435804 := by
    simpa [prefixWord, tailWord_3435804, baseEnd_3435804] using wordTrace_append hprefix tailTrace_3435804
  have hstable : (prefixWord ++ tailWord_3435804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435804).length < 2 ^ (prefixWord ++ tailWord_3435804).sum := by decide
  have hdescent : baseEnd_3435804 < baseStart_3435804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435824 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 3]
def baseStart_3435824 : Nat := 118140960795 + 3435824 * 2 ^ 59
def prefixEnd_3435824 : Nat := 4983230072969 + 3 ^ 40 * 3435824 * 2
def baseEnd_3435824 : Nat := 1764229156253470556498939

theorem tailTrace_3435824 : CollatzResearch.WordTrace tailWord_3435824 prefixEnd_3435824 1764229156253470556498939 := by
  unfold tailWord_3435824
  simp only [CollatzResearch.WordTrace]
  refine ⟨62657398152301957433705263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83543197536402609911607017 62657398152301957433705263)
  ·
    refine ⟨93986097228452936150557895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62657398152301957433705263 93986097228452936150557895)
    ·
      refine ⟨140979145842679404225836843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93986097228452936150557895 140979145842679404225836843)
      ·
        refine ⟨211468718764019106338755265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140979145842679404225836843 211468718764019106338755265)
        ·
          refine ⟨158601539073014329754066449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211468718764019106338755265 158601539073014329754066449)
          ·
            refine ⟨118951154304760747315549837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158601539073014329754066449 118951154304760747315549837)
            ·
              refine ⟨44606682864285280243331189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118951154304760747315549837 44606682864285280243331189)
              ·
                refine ⟨4181876518526745022812299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44606682864285280243331189 4181876518526745022812299)
                ·
                  refine ⟨6272814777790117534218449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4181876518526745022812299 6272814777790117534218449)
                  ·
                    refine ⟨4704611083342588150663837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6272814777790117534218449 4704611083342588150663837)
                    ·
                      refine ⟨1764229156253470556498939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4704611083342588150663837 1764229156253470556498939)
                      ·
                        rfl

theorem cell23_3435824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 3].length) (baseStart_3435824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435824 prefixEnd_3435824 := by exact prefixLift 3435824
  have htrace : WordTrace (prefixWord ++ tailWord_3435824) baseStart_3435824 baseEnd_3435824 := by
    simpa [prefixWord, tailWord_3435824, baseEnd_3435824] using wordTrace_append hprefix tailTrace_3435824
  have hstable : (prefixWord ++ tailWord_3435824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435824).length < 2 ^ (prefixWord ++ tailWord_3435824).sum := by decide
  have hdescent : baseEnd_3435824 < baseStart_3435824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435827 : List Nat := [1, 1, 1, 2, 5, 4, 9]
def baseStart_3435827 : Nat := 118140960795 + 3435827 * 2 ^ 59
def prefixEnd_3435827 : Nat := 4983230072969 + 3 ^ 40 * 3435827 * 2
def baseEnd_3435827 : Nat := 21780625885128815367425

theorem tailTrace_3435827 : CollatzResearch.WordTrace tailWord_3435827 prefixEnd_3435827 21780625885128815367425 := by
  unfold tailWord_3435827
  simp only [CollatzResearch.WordTrace]
  refine ⟨125314905723593046379769735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83543270482395364253179823 125314905723593046379769735)
  ·
    refine ⟨187972358585389569569654603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125314905723593046379769735 187972358585389569569654603)
    ·
      refine ⟨281958537878084354354481905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187972358585389569569654603 281958537878084354354481905)
      ·
        refine ⟨211468903408563265765861429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281958537878084354354481905 211468903408563265765861429)
        ·
          refine ⟨19825209694552806165549509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211468903408563265765861429 19825209694552806165549509)
          ·
            refine ⟨3717226817728651156040533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19825209694552806165549509 3717226817728651156040533)
            ·
              refine ⟨21780625885128815367425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3717226817728651156040533 21780625885128815367425)
              ·
                rfl

theorem cell23_3435827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 9].length) (baseStart_3435827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435827 prefixEnd_3435827 := by exact prefixLift 3435827
  have htrace : WordTrace (prefixWord ++ tailWord_3435827) baseStart_3435827 baseEnd_3435827 := by
    simpa [prefixWord, tailWord_3435827, baseEnd_3435827] using wordTrace_append hprefix tailTrace_3435827
  have hstable : (prefixWord ++ tailWord_3435827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435827).length < 2 ^ (prefixWord ++ tailWord_3435827).sum := by decide
  have hdescent : baseEnd_3435827 < baseStart_3435827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435844 : List Nat := [2, 3, 4, 1, 1, 1, 1, 10]
def baseStart_3435844 : Nat := 118140960795 + 3435844 * 2 ^ 59
def prefixEnd_3435844 : Nat := 4983230072969 + 3 ^ 40 * 3435844 * 2
def baseEnd_3435844 : Nat := 65342200958020758453661

theorem tailTrace_3435844 : CollatzResearch.WordTrace tailWord_3435844 prefixEnd_3435844 65342200958020758453661 := by
  unfold tailWord_3435844
  simp only [CollatzResearch.WordTrace]
  refine ⟨62657762882265729141569293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83543683843020972188759057 62657762882265729141569293)
  ·
    refine ⟨23496661080849648428088485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62657762882265729141569293 23496661080849648428088485)
    ·
      refine ⟨4405623952659309080266591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23496661080849648428088485 4405623952659309080266591)
      ·
        refine ⟨6608435928988963620399887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4405623952659309080266591 6608435928988963620399887)
        ·
          refine ⟨9912653893483445430599831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6608435928988963620399887 9912653893483445430599831)
          ·
            refine ⟨14868980840225168145899747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9912653893483445430599831 14868980840225168145899747)
            ·
              refine ⟨22303471260337752218849621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14868980840225168145899747 22303471260337752218849621)
              ·
                refine ⟨65342200958020758453661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22303471260337752218849621 65342200958020758453661)
                ·
                  rfl

theorem cell23_3435844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 10].length) (baseStart_3435844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435844 prefixEnd_3435844 := by exact prefixLift 3435844
  have htrace : WordTrace (prefixWord ++ tailWord_3435844) baseStart_3435844 baseEnd_3435844 := by
    simpa [prefixWord, tailWord_3435844, baseEnd_3435844] using wordTrace_append hprefix tailTrace_3435844
  have hstable : (prefixWord ++ tailWord_3435844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435844).length < 2 ^ (prefixWord ++ tailWord_3435844).sum := by decide
  have hdescent : baseEnd_3435844 < baseStart_3435844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435854 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_3435854 : Nat := 118140960795 + 3435854 * 2 ^ 59
def prefixEnd_3435854 : Nat := 4983230072969 + 3 ^ 40 * 3435854 * 2
def baseEnd_3435854 : Nat := 1764244560673105439123801

theorem tailTrace_3435854 : CollatzResearch.WordTrace tailWord_3435854 prefixEnd_3435854 1764244560673105439123801 := by
  unfold tailWord_3435854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15664486311811903748875327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83543926996330153327335077 15664486311811903748875327)
  ·
    refine ⟨23496729467717855623312991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15664486311811903748875327 23496729467717855623312991)
    ·
      refine ⟨35245094201576783434969487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23496729467717855623312991 35245094201576783434969487)
      ·
        refine ⟨52867641302365175152454231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35245094201576783434969487 52867641302365175152454231)
        ·
          refine ⟨79301461953547762728681347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52867641302365175152454231 79301461953547762728681347)
          ·
            refine ⟨118952192930321644093022021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79301461953547762728681347 118952192930321644093022021)
            ·
              refine ⟨22303536174435308267441629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118952192930321644093022021 22303536174435308267441629)
              ·
                refine ⟨8363826065413240600290611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22303536174435308267441629 8363826065413240600290611)
                ·
                  refine ⟨12545739098119860900435917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8363826065413240600290611 12545739098119860900435917)
                  ·
                    refine ⟨4704652161794947837663469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12545739098119860900435917 4704652161794947837663469)
                    ·
                      refine ⟨1764244560673105439123801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4704652161794947837663469 1764244560673105439123801)
                      ·
                        rfl

theorem cell23_3435854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_3435854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435854 prefixEnd_3435854 := by exact prefixLift 3435854
  have htrace : WordTrace (prefixWord ++ tailWord_3435854) baseStart_3435854 baseEnd_3435854 := by
    simpa [prefixWord, tailWord_3435854, baseEnd_3435854] using wordTrace_append hprefix tailTrace_3435854
  have hstable : (prefixWord ++ tailWord_3435854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435854).length < 2 ^ (prefixWord ++ tailWord_3435854).sum := by decide
  have hdescent : baseEnd_3435854 < baseStart_3435854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435887 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 2, 6]
def baseStart_3435887 : Nat := 118140960795 + 3435887 * 2 ^ 59
def prefixEnd_3435887 : Nat := 4983230072969 + 3 ^ 40 * 3435887 * 2
def baseEnd_3435887 : Nat := 588087168511567936670383

theorem tailTrace_3435887 : CollatzResearch.WordTrace tailWord_3435887 prefixEnd_3435887 588087168511567936670383 := by
  unfold tailWord_3435887
  simp only [CollatzResearch.WordTrace]
  refine ⟨125317094103375676626953915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83544729402250451084635943 125317094103375676626953915)
  ·
    refine ⟨187975641155063514940430873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125317094103375676626953915 187975641155063514940430873)
    ·
      refine ⟨140981730866297636205323155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187975641155063514940430873 140981730866297636205323155)
      ·
        refine ⟨211472596299446454307984733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140981730866297636205323155 211472596299446454307984733)
        ·
          refine ⟨79302223612292420365494275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211472596299446454307984733 79302223612292420365494275)
          ·
            refine ⟨118953335418438630548241413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79302223612292420365494275 118953335418438630548241413)
            ·
              refine ⟨22303750390957243227795265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118953335418438630548241413 22303750390957243227795265)
              ·
                refine ⟨16727812793217932420846449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22303750390957243227795265 16727812793217932420846449)
                ·
                  refine ⟨12545859594913449315634837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16727812793217932420846449 12545859594913449315634837)
                  ·
                    refine ⟨588087168511567936670383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12545859594913449315634837 588087168511567936670383)
                    ·
                      rfl

theorem cell23_3435887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_3435887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435887 prefixEnd_3435887 := by exact prefixLift 3435887
  have htrace : WordTrace (prefixWord ++ tailWord_3435887) baseStart_3435887 baseEnd_3435887 := by
    simpa [prefixWord, tailWord_3435887, baseEnd_3435887] using wordTrace_append hprefix tailTrace_3435887
  have hstable : (prefixWord ++ tailWord_3435887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435887).length < 2 ^ (prefixWord ++ tailWord_3435887).sum := by decide
  have hdescent : baseEnd_3435887 < baseStart_3435887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435897 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_3435897 : Nat := 118140960795 + 3435897 * 2 ^ 59
def prefixEnd_3435897 : Nat := 4983230072969 + 3 ^ 40 * 3435897 * 2
def baseEnd_3435897 : Nat := 1764266640341248770886103

theorem tailTrace_3435897 : CollatzResearch.WordTrace tailWord_3435897 prefixEnd_3435897 1764266640341248770886103 := by
  unfold tailWord_3435897
  simp only [CollatzResearch.WordTrace]
  refine ⟨125317458833339448334817945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83544972555559632223211963 125317458833339448334817945)
  ·
    refine ⟨93988094125004586251113459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125317458833339448334817945 93988094125004586251113459)
    ·
      refine ⟨140982141187506879376670189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93988094125004586251113459 140982141187506879376670189)
      ·
        refine ⟨52868302945315079766251321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140982141187506879376670189 52868302945315079766251321)
        ·
          refine ⟨39651227208986309824688491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52868302945315079766251321 39651227208986309824688491)
          ·
            refine ⟨59476840813479464737032737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39651227208986309824688491 59476840813479464737032737)
            ·
              refine ⟨44607630610109598552774553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59476840813479464737032737 44607630610109598552774553)
              ·
                refine ⟨33455722957582198914580915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44607630610109598552774553 33455722957582198914580915)
                ·
                  refine ⟨50183584436373298371871373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33455722957582198914580915 50183584436373298371871373)
                  ·
                    refine ⟨18818844163639986889451765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50183584436373298371871373 18818844163639986889451765)
                    ·
                      refine ⟨1764266640341248770886103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18818844163639986889451765 1764266640341248770886103)
                      ·
                        rfl

theorem cell23_3435897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_3435897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435897 prefixEnd_3435897 := by exact prefixLift 3435897
  have htrace : WordTrace (prefixWord ++ tailWord_3435897) baseStart_3435897 baseEnd_3435897 := by
    simpa [prefixWord, tailWord_3435897, baseEnd_3435897] using wordTrace_append hprefix tailTrace_3435897
  have hstable : (prefixWord ++ tailWord_3435897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435897).length < 2 ^ (prefixWord ++ tailWord_3435897).sum := by decide
  have hdescent : baseEnd_3435897 < baseStart_3435897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435911 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 1, 4, 2]
def baseStart_3435911 : Nat := 118140960795 + 3435911 * 2 ^ 59
def prefixEnd_3435911 : Nat := 4983230072969 + 3 ^ 40 * 3435911 * 2
def baseEnd_3435911 : Nat := 1764273829070411716111039

theorem tailTrace_3435911 : CollatzResearch.WordTrace tailWord_3435911 prefixEnd_3435911 1764273829070411716111039 := by
  unfold tailWord_3435911
  simp only [CollatzResearch.WordTrace]
  refine ⟨125317969455288728725827587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83545312970192485817218391 125317969455288728725827587)
  ·
    refine ⟨187976954182933093088741381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125317969455288728725827587 187976954182933093088741381)
    ·
      refine ⟨35245678909299954954139009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187976954182933093088741381 35245678909299954954139009)
      ·
        refine ⟨26434259181974966215604257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35245678909299954954139009 26434259181974966215604257)
        ·
          refine ⟨19825694386481224661703193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26434259181974966215604257 19825694386481224661703193)
          ·
            refine ⟨14869270789860918496277395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19825694386481224661703193 14869270789860918496277395)
            ·
              refine ⟨22303906184791377744416093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14869270789860918496277395 22303906184791377744416093)
              ·
                refine ⟨8363964819296766654156035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22303906184791377744416093 8363964819296766654156035)
                ·
                  refine ⟨12545947228945149981234053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8363964819296766654156035 12545947228945149981234053)
                  ·
                    refine ⟨2352365105427215621481385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12545947228945149981234053 2352365105427215621481385)
                    ·
                      refine ⟨1764273829070411716111039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352365105427215621481385 1764273829070411716111039)
                      ·
                        rfl

theorem cell23_3435911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_3435911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435911 prefixEnd_3435911 := by exact prefixLift 3435911
  have htrace : WordTrace (prefixWord ++ tailWord_3435911) baseStart_3435911 baseEnd_3435911 := by
    simpa [prefixWord, tailWord_3435911, baseEnd_3435911] using wordTrace_append hprefix tailTrace_3435911
  have hstable : (prefixWord ++ tailWord_3435911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435911).length < 2 ^ (prefixWord ++ tailWord_3435911).sum := by decide
  have hdescent : baseEnd_3435911 < baseStart_3435911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435927 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_3435927 : Nat := 118140960795 + 3435927 * 2 ^ 59
def prefixEnd_3435927 : Nat := 4983230072969 + 3 ^ 40 * 3435927 * 2
def baseEnd_3435927 : Nat := 1764282044760883653510965

theorem tailTrace_3435927 : CollatzResearch.WordTrace tailWord_3435927 prefixEnd_3435927 1764282044760883653510965 := by
  unfold tailWord_3435927
  simp only [CollatzResearch.WordTrace]
  refine ⟨125318553023230763458410035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83545702015487175638940023 125318553023230763458410035)
  ·
    refine ⟨187977829534846145187615053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125318553023230763458410035 187977829534846145187615053)
    ·
      refine ⟨70491686075567304445355645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187977829534846145187615053 70491686075567304445355645)
      ·
        refine ⟨26434382278337739167008367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70491686075567304445355645 26434382278337739167008367)
        ·
          refine ⟨39651573417506608750512551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26434382278337739167008367 39651573417506608750512551)
          ·
            refine ⟨59477360126259913125768827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39651573417506608750512551 59477360126259913125768827)
            ·
              refine ⟨89216040189389869688653241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59477360126259913125768827 89216040189389869688653241)
              ·
                refine ⟨66912030142042402266489931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89216040189389869688653241 66912030142042402266489931)
                ·
                  refine ⟨100368045213063603399734897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66912030142042402266489931 100368045213063603399734897)
                  ·
                    refine ⟨75276033909797702549801173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100368045213063603399734897 75276033909797702549801173)
                    ·
                      refine ⟨1764282044760883653510965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75276033909797702549801173 1764282044760883653510965)
                      ·
                        rfl

theorem cell23_3435927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_3435927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435927 prefixEnd_3435927 := by exact prefixLift 3435927
  have htrace : WordTrace (prefixWord ++ tailWord_3435927) baseStart_3435927 baseEnd_3435927 := by
    simpa [prefixWord, tailWord_3435927, baseEnd_3435927] using wordTrace_append hprefix tailTrace_3435927
  have hstable : (prefixWord ++ tailWord_3435927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435927).length < 2 ^ (prefixWord ++ tailWord_3435927).sum := by decide
  have hdescent : baseEnd_3435927 < baseStart_3435927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435977 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 1, 10]
def baseStart_3435977 : Nat := 118140960795 + 3435977 * 2 ^ 59
def prefixEnd_3435977 : Nat := 4983230072969 + 3 ^ 40 * 3435977 * 2
def baseEnd_3435977 : Nat := 588102572931202819295245

theorem tailTrace_3435977 : CollatzResearch.WordTrace tailWord_3435977 prefixEnd_3435977 588102572931202819295245 := by
  unfold tailWord_3435977
  simp only [CollatzResearch.WordTrace]
  refine ⟨125320376673049621997730185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83546917782033081331820123 125320376673049621997730185)
  ·
    refine ⟨93990282504787216498297639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125320376673049621997730185 93990282504787216498297639)
    ·
      refine ⟨140985423757180824747446459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93990282504787216498297639 140985423757180824747446459)
      ·
        refine ⟨211478135635771237121169689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140985423757180824747446459 211478135635771237121169689)
        ·
          refine ⟨158608601726828427840877267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211478135635771237121169689 158608601726828427840877267)
          ·
            refine ⟨237912902590242641761315901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158608601726828427840877267 237912902590242641761315901)
            ·
              refine ⟨89217338471340990660493463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237912902590242641761315901 89217338471340990660493463)
              ·
                refine ⟨133826007707011485990740195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89217338471340990660493463 133826007707011485990740195)
                ·
                  refine ⟨200739011560517228986110293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133826007707011485990740195 200739011560517228986110293)
                  ·
                    refine ⟨588102572931202819295245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 200739011560517228986110293 588102572931202819295245)
                    ·
                      rfl

theorem cell23_3435977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_3435977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3435977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3435977 prefixEnd_3435977 := by exact prefixLift 3435977
  have htrace : WordTrace (prefixWord ++ tailWord_3435977) baseStart_3435977 baseEnd_3435977 := by
    simpa [prefixWord, tailWord_3435977, baseEnd_3435977] using wordTrace_append hprefix tailTrace_3435977
  have hstable : (prefixWord ++ tailWord_3435977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435977).length < 2 ^ (prefixWord ++ tailWord_3435977).sum := by decide
  have hdescent : baseEnd_3435977 < baseStart_3435977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436001 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_3436001 : Nat := 118140960795 + 3436001 * 2 ^ 59
def prefixEnd_3436001 : Nat := 4983230072969 + 3 ^ 40 * 3436001 * 2
def baseEnd_3436001 : Nat := 1764320042329316363985625

theorem tailTrace_3436001 : CollatzResearch.WordTrace tailWord_3436001 prefixEnd_3436001 1764320042329316363985625 := by
  unfold tailWord_3436001
  simp only [CollatzResearch.WordTrace]
  refine ⟨125321252024962674096603857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83547501349975116064402571 125321252024962674096603857)
  ·
    refine ⟨93990939018722005572452893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125321252024962674096603857 93990939018722005572452893)
    ·
      refine ⟨35246602132020752089669835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93990939018722005572452893 35246602132020752089669835)
      ·
        refine ⟨52869903198031128134504753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35246602132020752089669835 52869903198031128134504753)
        ·
          refine ⟨39652427398523346100878565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52869903198031128134504753 39652427398523346100878565)
          ·
            refine ⟨7434830137223127393914731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39652427398523346100878565 7434830137223127393914731)
            ·
              refine ⟨11152245205834691090872097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7434830137223127393914731 11152245205834691090872097)
              ·
                refine ⟨8364183904376018318154073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11152245205834691090872097 8364183904376018318154073)
                ·
                  refine ⟨6273137928282013738615555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8364183904376018318154073 6273137928282013738615555)
                  ·
                    refine ⟨9409706892423020607923333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273137928282013738615555 9409706892423020607923333)
                    ·
                      refine ⟨1764320042329316363985625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9409706892423020607923333 1764320042329316363985625)
                      ·
                        rfl

theorem cell23_3436001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_3436001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436001 prefixEnd_3436001 := by exact prefixLift 3436001
  have htrace : WordTrace (prefixWord ++ tailWord_3436001) baseStart_3436001 baseEnd_3436001 := by
    simpa [prefixWord, tailWord_3436001, baseEnd_3436001] using wordTrace_append hprefix tailTrace_3436001
  have hstable : (prefixWord ++ tailWord_3436001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436001).length < 2 ^ (prefixWord ++ tailWord_3436001).sum := by decide
  have hdescent : baseEnd_3436001 < baseStart_3436001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436095 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 2, 3, 2]
def baseStart_3436095 : Nat := 118140960795 + 3436095 * 2 ^ 59
def prefixEnd_3436095 : Nat := 4983230072969 + 3 ^ 40 * 3436095 * 2
def baseEnd_3436095 : Nat := 1764368309510838996210193

theorem tailTrace_3436095 : CollatzResearch.WordTrace tailWord_3436095 prefixEnd_3436095 1764368309510838996210193 := by
  unfold tailWord_3436095
  simp only [CollatzResearch.WordTrace]
  refine ⟨125324680486622128150525739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83549786991081418767017159 125324680486622128150525739)
  ·
    refine ⟨187987020729933192225788609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125324680486622128150525739 187987020729933192225788609)
    ·
      refine ⟨140990265547449894169341457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187987020729933192225788609 140990265547449894169341457)
      ·
        refine ⟨105742699160587420627006093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140990265547449894169341457 105742699160587420627006093)
        ·
          refine ⟨39653512185220282735127285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105742699160587420627006093 39653512185220282735127285)
          ·
            refine ⟨3717516767364401506418183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39653512185220282735127285 3717516767364401506418183)
            ·
              refine ⟨5576275151046602259627275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3717516767364401506418183 5576275151046602259627275)
              ·
                refine ⟨8364412726569903389440913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5576275151046602259627275 8364412726569903389440913)
                ·
                  refine ⟨6273309544927427542080685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8364412726569903389440913 6273309544927427542080685)
                  ·
                    refine ⟨2352491079347785328280257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6273309544927427542080685 2352491079347785328280257)
                    ·
                      refine ⟨1764368309510838996210193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2352491079347785328280257 1764368309510838996210193)
                      ·
                        rfl

theorem cell23_3436095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 3, 2].length) (baseStart_3436095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436095 prefixEnd_3436095 := by exact prefixLift 3436095
  have htrace : WordTrace (prefixWord ++ tailWord_3436095) baseStart_3436095 baseEnd_3436095 := by
    simpa [prefixWord, tailWord_3436095, baseEnd_3436095] using wordTrace_append hprefix tailTrace_3436095
  have hstable : (prefixWord ++ tailWord_3436095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436095).length < 2 ^ (prefixWord ++ tailWord_3436095).sum := by decide
  have hdescent : baseEnd_3436095 < baseStart_3436095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436101 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 4, 4]
def baseStart_3436101 : Nat := 118140960795 + 3436101 * 2 ^ 59
def prefixEnd_3436101 : Nat := 4983230072969 + 3 ^ 40 * 3436101 * 2
def baseEnd_3436101 : Nat := 588123796798255324245055

theorem tailTrace_3436101 : CollatzResearch.WordTrace tailWord_3436101 prefixEnd_3436101 588123796798255324245055 := by
  unfold tailWord_3436101
  simp only [CollatzResearch.WordTrace]
  refine ⟨125324899324600391175244157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83549932883066927450162771 125324899324600391175244157)
  ·
    refine ⟨46996837246725146690716559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125324899324600391175244157 46996837246725146690716559)
    ·
      refine ⟨70495255870087720036074839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46996837246725146690716559 70495255870087720036074839)
      ·
        refine ⟨105742883805131580054112259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70495255870087720036074839 105742883805131580054112259)
        ·
          refine ⟨158614325707697370081168389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105742883805131580054112259 158614325707697370081168389)
          ·
            refine ⟨29740186070193256890219073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158614325707697370081168389 29740186070193256890219073)
            ·
              refine ⟨22305139552644942667664305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29740186070193256890219073 22305139552644942667664305)
              ·
                refine ⟨16728854664483707000748229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22305139552644942667664305 16728854664483707000748229)
                ·
                  refine ⟨3136660249590695062640293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16728854664483707000748229 3136660249590695062640293)
                  ·
                    refine ⟨588123796798255324245055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3136660249590695062640293 588123796798255324245055)
                    ·
                      rfl

theorem cell23_3436101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_3436101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436101 prefixEnd_3436101 := by exact prefixLift 3436101
  have htrace : WordTrace (prefixWord ++ tailWord_3436101) baseStart_3436101 baseEnd_3436101 := by
    simpa [prefixWord, tailWord_3436101, baseEnd_3436101] using wordTrace_append hprefix tailTrace_3436101
  have hstable : (prefixWord ++ tailWord_3436101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436101).length < 2 ^ (prefixWord ++ tailWord_3436101).sum := by decide
  have hdescent : baseEnd_3436101 < baseStart_3436101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436104 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_3436104 : Nat := 118140960795 + 3436104 * 2 ^ 59
def prefixEnd_3436104 : Nat := 4983230072969 + 3 ^ 40 * 3436104 * 2
def baseEnd_3436104 : Nat := 1764372930836729460997651

theorem tailTrace_3436104 : CollatzResearch.WordTrace tailWord_3436104 prefixEnd_3436104 1764372930836729460997651 := by
  unfold tailWord_3436104
  simp only [CollatzResearch.WordTrace]
  refine ⟨62662504371794761343801683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83550005829059681791735577 62662504371794761343801683)
  ·
    refine ⟨93993756557692142015702525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62662504371794761343801683 93993756557692142015702525)
    ·
      refine ⟨35247658709134553255888447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93993756557692142015702525 35247658709134553255888447)
      ·
        refine ⟨52871488063701829883832671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35247658709134553255888447 52871488063701829883832671)
        ·
          refine ⟨79307232095552744825749007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52871488063701829883832671 79307232095552744825749007)
          ·
            refine ⟨118960848143329117238623511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79307232095552744825749007 118960848143329117238623511)
            ·
              refine ⟨178441272214993675857935267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118960848143329117238623511 178441272214993675857935267)
              ·
                refine ⟨267661908322490513786902901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178441272214993675857935267 267661908322490513786902901)
                ·
                  refine ⟨25093303905233485667522147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 267661908322490513786902901 25093303905233485667522147)
                  ·
                    refine ⟨37639955857850228501283221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25093303905233485667522147 37639955857850228501283221)
                    ·
                      refine ⟨1764372930836729460997651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37639955857850228501283221 1764372930836729460997651)
                      ·
                        rfl

theorem cell23_3436104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_3436104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3436104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3436104 prefixEnd_3436104 := by exact prefixLift 3436104
  have htrace : WordTrace (prefixWord ++ tailWord_3436104) baseStart_3436104 baseEnd_3436104 := by
    simpa [prefixWord, tailWord_3436104, baseEnd_3436104] using wordTrace_append hprefix tailTrace_3436104
  have hstable : (prefixWord ++ tailWord_3436104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436104).length < 2 ^ (prefixWord ++ tailWord_3436104).sum := by decide
  have hdescent : baseEnd_3436104 < baseStart_3436104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
