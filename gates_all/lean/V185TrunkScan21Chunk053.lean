import V185TrunkScan21Chunk052

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_640504 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 4]
def baseStart_640504 : Nat := 118140960795 + 640504 * 2 ^ 59
def prefixEnd_640504 : Nat := 4983230072969 + 3 ^ 40 * 640504 * 2
def baseEnd_640504 : Nat := 146171739167763226157503

theorem tailTrace_640504 : CollatzResearch.WordTrace tailWord_640504 prefixEnd_640504 146171739167763226157503 := by
  unfold tailWord_640504
  simp only [CollatzResearch.WordTrace]
  refine ⟨11680550035785436109688283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15574066714380581479584377 11680550035785436109688283)
  ·
    refine ⟨17520825053678154164532425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11680550035785436109688283 17520825053678154164532425)
    ·
      refine ⟨13140618790258615623399319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17520825053678154164532425 13140618790258615623399319)
      ·
        refine ⟨19710928185387923435098979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13140618790258615623399319 19710928185387923435098979)
        ·
          refine ⟨29566392278081885152648469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19710928185387923435098979 29566392278081885152648469)
          ·
            refine ⟨1385924638035088366530397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29566392278081885152648469 1385924638035088366530397)
            ·
              refine ⟨519721739263158137448899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1385924638035088366530397 519721739263158137448899)
              ·
                refine ⟨779582608894737206173349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519721739263158137448899 779582608894737206173349)
                ·
                  refine ⟨146171739167763226157503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779582608894737206173349 146171739167763226157503)
                  ·
                    rfl

theorem cell21_640504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_640504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640504 prefixEnd_640504 := by exact prefixLift 640504
  have htrace : WordTrace (prefixWord ++ tailWord_640504) baseStart_640504 baseEnd_640504 := by
    simpa [prefixWord, tailWord_640504, baseEnd_640504] using wordTrace_append hprefix tailTrace_640504
  have hstable : (prefixWord ++ tailWord_640504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640504).length < 2 ^ (prefixWord ++ tailWord_640504).sum := by decide
  have hdescent : baseEnd_640504 < baseStart_640504 := by decide
  rcases family_descends (prefixWord ++ tailWord_640504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640515 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 7]
def baseStart_640515 : Nat := 118140960795 + 640515 * 2 ^ 59
def prefixEnd_640515 : Nat := 4983230072969 + 3 ^ 40 * 640515 * 2
def baseEnd_640515 : Nat := 146174249517629651474147

theorem tailTrace_640515 : CollatzResearch.WordTrace tailWord_640515 prefixEnd_640515 146174249517629651474147 := by
  unfold tailWord_640515
  simp only [CollatzResearch.WordTrace]
  refine ⟨23361501274531021098026999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15574334183020680732017999 23361501274531021098026999)
  ·
    refine ⟨35042251911796531647040499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23361501274531021098026999 35042251911796531647040499)
    ·
      refine ⟨52563377867694797470560749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35042251911796531647040499 52563377867694797470560749)
      ·
        refine ⟨19711266700385549051460281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52563377867694797470560749 19711266700385549051460281)
        ·
          refine ⟨14783450025289161788595211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19711266700385549051460281 14783450025289161788595211)
          ·
            refine ⟨22175175037933742682892817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14783450025289161788595211 22175175037933742682892817)
            ·
              refine ⟨16631381278450307012169613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22175175037933742682892817 16631381278450307012169613)
              ·
                refine ⟨6236767979418865129563605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16631381278450307012169613 6236767979418865129563605)
                ·
                  refine ⟨146174249517629651474147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6236767979418865129563605 146174249517629651474147)
                  ·
                    rfl

theorem cell21_640515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_640515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640515 prefixEnd_640515 := by exact prefixLift 640515
  have htrace : WordTrace (prefixWord ++ tailWord_640515) baseStart_640515 baseEnd_640515 := by
    simpa [prefixWord, tailWord_640515, baseEnd_640515] using wordTrace_append hprefix tailTrace_640515
  have hstable : (prefixWord ++ tailWord_640515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640515).length < 2 ^ (prefixWord ++ tailWord_640515).sum := by decide
  have hdescent : baseEnd_640515 < baseStart_640515 := by decide
  rcases family_descends (prefixWord ++ tailWord_640515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640563 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 4]
def baseStart_640563 : Nat := 118140960795 + 640563 * 2 ^ 59
def prefixEnd_640563 : Nat := 4983230072969 + 3 ^ 40 * 640563 * 2
def baseEnd_640563 : Nat := 146185203771592234674049

theorem tailTrace_640563 : CollatzResearch.WordTrace tailWord_640563 prefixEnd_640563 146185203771592234674049 := by
  unfold tailWord_640563
  simp only [CollatzResearch.WordTrace]
  refine ⟨23363251978357125295774343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15575501318904750197182895 23363251978357125295774343)
  ·
    refine ⟨35044877967535687943661515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23363251978357125295774343 35044877967535687943661515)
    ·
      refine ⟨52567316951303531915492273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35044877967535687943661515 52567316951303531915492273)
      ·
        refine ⟨39425487713477648936619205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52567316951303531915492273 39425487713477648936619205)
        ·
          refine ⟨7392278946277059175616101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39425487713477648936619205 7392278946277059175616101)
          ·
            refine ⟨1386052302426948595428019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7392278946277059175616101 1386052302426948595428019)
            ·
              refine ⟨2079078453640422893142029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1386052302426948595428019 2079078453640422893142029)
              ·
                refine ⟨779654420115158584928261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2079078453640422893142029 779654420115158584928261)
                ·
                  refine ⟨146185203771592234674049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779654420115158584928261 146185203771592234674049)
                  ·
                    rfl

theorem cell21_640563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 4].length) (baseStart_640563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640563 prefixEnd_640563 := by exact prefixLift 640563
  have htrace : WordTrace (prefixWord ++ tailWord_640563) baseStart_640563 baseEnd_640563 := by
    simpa [prefixWord, tailWord_640563, baseEnd_640563] using wordTrace_append hprefix tailTrace_640563
  have hstable : (prefixWord ++ tailWord_640563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640563).length < 2 ^ (prefixWord ++ tailWord_640563).sum := by decide
  have hdescent : baseEnd_640563 < baseStart_640563 := by decide
  rcases family_descends (prefixWord ++ tailWord_640563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640577 : List Nat := [1, 2, 5, 1, 1, 1, 1, 9]
def baseStart_640577 : Nat := 118140960795 + 640577 * 2 ^ 59
def prefixEnd_640577 : Nat := 4983230072969 + 3 ^ 40 * 640577 * 2
def baseEnd_640577 : Nat := 48729466254110440480229

theorem tailTrace_640577 : CollatzResearch.WordTrace tailWord_640577 prefixEnd_640577 48729466254110440480229 := by
  unfold tailWord_640577
  simp only [CollatzResearch.WordTrace]
  refine ⟨23363762600306405686783985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15575841733537603791189323 23363762600306405686783985)
  ·
    refine ⟨17522821950229804265087989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23363762600306405686783985 17522821950229804265087989)
    ·
      refine ⟨1642764557834044149851999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17522821950229804265087989 1642764557834044149851999)
      ·
        refine ⟨2464146836751066224777999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1642764557834044149851999 2464146836751066224777999)
        ·
          refine ⟨3696220255126599337166999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2464146836751066224777999 3696220255126599337166999)
          ·
            refine ⟨5544330382689899005750499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696220255126599337166999 5544330382689899005750499)
            ·
              refine ⟨8316495574034848508625749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5544330382689899005750499 8316495574034848508625749)
              ·
                refine ⟨48729466254110440480229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8316495574034848508625749 48729466254110440480229)
                ·
                  rfl

theorem cell21_640577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 9].length) (baseStart_640577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640577 prefixEnd_640577 := by exact prefixLift 640577
  have htrace : WordTrace (prefixWord ++ tailWord_640577) baseStart_640577 baseEnd_640577 := by
    simpa [prefixWord, tailWord_640577, baseEnd_640577] using wordTrace_append hprefix tailTrace_640577
  have hstable : (prefixWord ++ tailWord_640577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640577).length < 2 ^ (prefixWord ++ tailWord_640577).sum := by decide
  have hdescent : baseEnd_640577 < baseStart_640577 := by decide
  rcases family_descends (prefixWord ++ tailWord_640577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640698 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_640698 : Nat := 118140960795 + 640698 * 2 ^ 59
def prefixEnd_640698 : Nat := 4983230072969 + 3 ^ 40 * 640698 * 2
def baseEnd_640698 : Nat := 146216012610861999923773

theorem tailTrace_640698 : CollatzResearch.WordTrace tailWord_640698 prefixEnd_640698 146216012610861999923773 := by
  unfold tailWord_640698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5842043958217010837984687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15578783888578695567959165 5842043958217010837984687)
  ·
    refine ⟨8763065937325516256977031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5842043958217010837984687 8763065937325516256977031)
    ·
      refine ⟨13144598905988274385465547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8763065937325516256977031 13144598905988274385465547)
      ·
        refine ⟨19716898358982411578198321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13144598905988274385465547 19716898358982411578198321)
        ·
          refine ⟨14787673769236808683648741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19716898358982411578198321 14787673769236808683648741)
          ·
            refine ⟨2772688831731901628184139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14787673769236808683648741 2772688831731901628184139)
            ·
              refine ⟨4159033247597852442276209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772688831731901628184139 4159033247597852442276209)
              ·
                refine ⟨3119274935698389331707157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4159033247597852442276209 3119274935698389331707157)
                ·
                  refine ⟨146216012610861999923773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3119274935698389331707157 146216012610861999923773)
                  ·
                    rfl

theorem cell21_640698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_640698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640698 prefixEnd_640698 := by exact prefixLift 640698
  have htrace : WordTrace (prefixWord ++ tailWord_640698) baseStart_640698 baseEnd_640698 := by
    simpa [prefixWord, tailWord_640698, baseEnd_640698] using wordTrace_append hprefix tailTrace_640698
  have hstable : (prefixWord ++ tailWord_640698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640698).length < 2 ^ (prefixWord ++ tailWord_640698).sum := by decide
  have hdescent : baseEnd_640698 < baseStart_640698 := by decide
  rcases family_descends (prefixWord ++ tailWord_640698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640718 : List Nat := [4, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_640718 : Nat := 118140960795 + 640718 * 2 ^ 59
def prefixEnd_640718 : Nat := 4983230072969 + 3 ^ 40 * 640718 * 2
def baseEnd_640718 : Nat := 146220576883346409590399

theorem tailTrace_640718 : CollatzResearch.WordTrace tailWord_640718 prefixEnd_640718 146220576883346409590399 := by
  unfold tailWord_640718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921113161599448345958351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15579270195197057845111205 2921113161599448345958351)
  ·
    refine ⟨4381669742399172518937527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2921113161599448345958351 4381669742399172518937527)
    ·
      refine ⟨6572504613598758778406291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4381669742399172518937527 6572504613598758778406291)
      ·
        refine ⟨9858756920398138167609437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6572504613598758778406291 9858756920398138167609437)
        ·
          refine ⟨3697033845149301812853539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9858756920398138167609437 3697033845149301812853539)
          ·
            refine ⟨5545550767723952719280309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697033845149301812853539 5545550767723952719280309)
            ·
              refine ⟨519895384474120567432529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5545550767723952719280309 519895384474120567432529)
              ·
                refine ⟨389921538355590425574397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519895384474120567432529 389921538355590425574397)
                ·
                  refine ⟨146220576883346409590399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389921538355590425574397 146220576883346409590399)
                  ·
                    rfl

theorem cell21_640718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_640718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640718 prefixEnd_640718 := by exact prefixLift 640718
  have htrace : WordTrace (prefixWord ++ tailWord_640718) baseStart_640718 baseEnd_640718 := by
    simpa [prefixWord, tailWord_640718, baseEnd_640718] using wordTrace_append hprefix tailTrace_640718
  have hstable : (prefixWord ++ tailWord_640718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640718).length < 2 ^ (prefixWord ++ tailWord_640718).sum := by decide
  have hdescent : baseEnd_640718 < baseStart_640718 := by decide
  rcases family_descends (prefixWord ++ tailWord_640718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640729 : List Nat := [1, 2, 1, 2, 3, 4, 2, 6]
def baseStart_640729 : Nat := 118140960795 + 640729 * 2 ^ 59
def prefixEnd_640729 : Nat := 4983230072969 + 3 ^ 40 * 640729 * 2
def baseEnd_640729 : Nat := 48741029077737611635681

theorem tailTrace_640729 : CollatzResearch.WordTrace tailWord_640729 prefixEnd_640729 48741029077737611635681 := by
  unfold tailWord_640729
  simp only [CollatzResearch.WordTrace]
  refine ⟨23369306495755735646317241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15579537663837157097544827 23369306495755735646317241)
  ·
    refine ⟨17526979871816801734737931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23369306495755735646317241 17526979871816801734737931)
    ·
      refine ⟨26290469807725202602106897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17526979871816801734737931 26290469807725202602106897)
      ·
        refine ⟨19717852355793901951580173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26290469807725202602106897 19717852355793901951580173)
        ·
          refine ⟨7394194633422713231842565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19717852355793901951580173 7394194633422713231842565)
          ·
            refine ⟨1386411493766758730970481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7394194633422713231842565 1386411493766758730970481)
            ·
              refine ⟨1039808620325069048227861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1386411493766758730970481 1039808620325069048227861)
              ·
                refine ⟨48741029077737611635681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1039808620325069048227861 48741029077737611635681)
                ·
                  rfl

theorem cell21_640729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 6].length) (baseStart_640729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640729 prefixEnd_640729 := by exact prefixLift 640729
  have htrace : WordTrace (prefixWord ++ tailWord_640729) baseStart_640729 baseEnd_640729 := by
    simpa [prefixWord, tailWord_640729, baseEnd_640729] using wordTrace_append hprefix tailTrace_640729
  have hstable : (prefixWord ++ tailWord_640729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640729).length < 2 ^ (prefixWord ++ tailWord_640729).sum := by decide
  have hdescent : baseEnd_640729 < baseStart_640729 := by decide
  rcases family_descends (prefixWord ++ tailWord_640729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640791 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 4]
def baseStart_640791 : Nat := 118140960795 + 640791 * 2 ^ 59
def prefixEnd_640791 : Nat := 4983230072969 + 3 ^ 40 * 640791 * 2
def baseEnd_640791 : Nat := 146237236477914504873583

theorem tailTrace_640791 : CollatzResearch.WordTrace tailWord_640791 prefixEnd_640791 146237236477914504873583 := by
  unfold tailWord_640791
  simp only [CollatzResearch.WordTrace]
  refine ⟨23371567821531120235074227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15581045214354080156716151 23371567821531120235074227)
  ·
    refine ⟨35057351732296680352611341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23371567821531120235074227 35057351732296680352611341)
    ·
      refine ⟨13146506899611255132229253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35057351732296680352611341 13146506899611255132229253)
      ·
        refine ⟨2464970043677110337292985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13146506899611255132229253 2464970043677110337292985)
        ·
          refine ⟨1848727532757832752969739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2464970043677110337292985 1848727532757832752969739)
          ·
            refine ⟨2773091299136749129454609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848727532757832752969739 2773091299136749129454609)
            ·
              refine ⟨2079818474352561847090957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2773091299136749129454609 2079818474352561847090957)
              ·
                refine ⟨779931927882210692659109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2079818474352561847090957 779931927882210692659109)
                ·
                  refine ⟨146237236477914504873583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779931927882210692659109 146237236477914504873583)
                  ·
                    rfl

theorem cell21_640791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 4].length) (baseStart_640791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640791 prefixEnd_640791 := by exact prefixLift 640791
  have htrace : WordTrace (prefixWord ++ tailWord_640791) baseStart_640791 baseEnd_640791 := by
    simpa [prefixWord, tailWord_640791, baseEnd_640791] using wordTrace_append hprefix tailTrace_640791
  have hstable : (prefixWord ++ tailWord_640791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640791).length < 2 ^ (prefixWord ++ tailWord_640791).sum := by decide
  have hdescent : baseEnd_640791 < baseStart_640791 := by decide
  rcases family_descends (prefixWord ++ tailWord_640791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640822 : List Nat := [5, 1, 2, 2, 1, 2, 8]
def baseStart_640822 : Nat := 118140960795 + 640822 * 2 ^ 59
def prefixEnd_640822 : Nat := 4983230072969 + 3 ^ 40 * 640822 * 2
def baseEnd_640822 : Nat := 16249367900029482206317

theorem tailTrace_640822 : CollatzResearch.WordTrace tailWord_640822 prefixEnd_640822 16249367900029482206317 := by
  unfold tailWord_640822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460793655276175783090795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15581798989612541686301813 1460793655276175783090795)
  ·
    refine ⟨2191190482914263674636193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1460793655276175783090795 2191190482914263674636193)
    ·
      refine ⟨1643392862185697755977145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2191190482914263674636193 1643392862185697755977145)
      ·
        refine ⟨1232544646639273316982859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1643392862185697755977145 1232544646639273316982859)
        ·
          refine ⟨1848816969958909975474289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232544646639273316982859 1848816969958909975474289)
          ·
            refine ⟨1386612727469182481605717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1848816969958909975474289 1386612727469182481605717)
            ·
              refine ⟨16249367900029482206317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1386612727469182481605717 16249367900029482206317)
              ·
                rfl

theorem cell21_640822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 8].length) (baseStart_640822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640822 prefixEnd_640822 := by exact prefixLift 640822
  have htrace : WordTrace (prefixWord ++ tailWord_640822) baseStart_640822 baseEnd_640822 := by
    simpa [prefixWord, tailWord_640822, baseEnd_640822] using wordTrace_append hprefix tailTrace_640822
  have hstable : (prefixWord ++ tailWord_640822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640822).length < 2 ^ (prefixWord ++ tailWord_640822).sum := by decide
  have hdescent : baseEnd_640822 < baseStart_640822 := by decide
  rcases family_descends (prefixWord ++ tailWord_640822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640825 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 4]
def baseStart_640825 : Nat := 118140960795 + 640825 * 2 ^ 59
def prefixEnd_640825 : Nat := 4983230072969 + 3 ^ 40 * 640825 * 2
def baseEnd_640825 : Nat := 146244995741138001306847

theorem tailTrace_640825 : CollatzResearch.WordTrace tailWord_640825 prefixEnd_640825 146244995741138001306847 := by
  unfold tailWord_640825
  simp only [CollatzResearch.WordTrace]
  refine ⟨23372807903407944041811929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15581871935605296027874619 23372807903407944041811929)
  ·
    refine ⟨17529605927555958031358947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23372807903407944041811929 17529605927555958031358947)
    ·
      refine ⟨26294408891333937047038421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17529605927555958031358947 26294408891333937047038421)
      ·
        refine ⟨616275208390639149539963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 26294408891333937047038421 616275208390639149539963)
        ·
          refine ⟨924412812585958724309945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616275208390639149539963 924412812585958724309945)
          ·
            refine ⟨693309609439469043232459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 924412812585958724309945 693309609439469043232459)
            ·
              refine ⟨1039964414159203564848689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693309609439469043232459 1039964414159203564848689)
              ·
                refine ⟨779973310619402673636517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039964414159203564848689 779973310619402673636517)
                ·
                  refine ⟨146244995741138001306847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779973310619402673636517 146244995741138001306847)
                  ·
                    rfl

theorem cell21_640825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_640825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640825 prefixEnd_640825 := by exact prefixLift 640825
  have htrace : WordTrace (prefixWord ++ tailWord_640825) baseStart_640825 baseEnd_640825 := by
    simpa [prefixWord, tailWord_640825, baseEnd_640825] using wordTrace_append hprefix tailTrace_640825
  have hstable : (prefixWord ++ tailWord_640825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640825).length < 2 ^ (prefixWord ++ tailWord_640825).sum := by decide
  have hdescent : baseEnd_640825 < baseStart_640825 := by decide
  rcases family_descends (prefixWord ++ tailWord_640825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640957 : List Nat := [1, 4, 1, 2, 3, 1, 3, 6]
def baseStart_640957 : Nat := 118140960795 + 640957 * 2 ^ 59
def prefixEnd_640957 : Nat := 4983230072969 + 3 ^ 40 * 640957 * 2
def baseEnd_640957 : Nat := 48758373313178368368859

theorem tailTrace_640957 : CollatzResearch.WordTrace tailWord_640957 prefixEnd_640957 48758373313178368368859 := by
  unfold tailWord_640957
  simp only [CollatzResearch.WordTrace]
  refine ⟨23377622338929730585617125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15585081559286487057078083 23377622338929730585617125)
  ·
    refine ⟨4383304188549324484803211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23377622338929730585617125 4383304188549324484803211)
    ·
      refine ⟨6574956282823986727204817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4383304188549324484803211 6574956282823986727204817)
      ·
        refine ⟨4931217212117990045403613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6574956282823986727204817 4931217212117990045403613)
        ·
          refine ⟨1849206454544246267026355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4931217212117990045403613 1849206454544246267026355)
          ·
            refine ⟨2773809681816369400539533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849206454544246267026355 2773809681816369400539533)
            ·
              refine ⟨1040178630681138525202325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2773809681816369400539533 1040178630681138525202325)
              ·
                refine ⟨48758373313178368368859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1040178630681138525202325 48758373313178368368859)
                ·
                  rfl

theorem cell21_640957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 6].length) (baseStart_640957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640957 prefixEnd_640957 := by exact prefixLift 640957
  have htrace : WordTrace (prefixWord ++ tailWord_640957) baseStart_640957 baseEnd_640957 := by
    simpa [prefixWord, tailWord_640957, baseEnd_640957] using wordTrace_append hprefix tailTrace_640957
  have hstable : (prefixWord ++ tailWord_640957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640957).length < 2 ^ (prefixWord ++ tailWord_640957).sum := by decide
  have hdescent : baseEnd_640957 < baseStart_640957 := by decide
  rcases family_descends (prefixWord ++ tailWord_640957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640971 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 5]
def baseStart_640971 : Nat := 118140960795 + 640971 * 2 ^ 59
def prefixEnd_640971 : Nat := 4983230072969 + 3 ^ 40 * 640971 * 2
def baseEnd_640971 : Nat := 146278314930274191873215

theorem tailTrace_640971 : CollatzResearch.WordTrace tailWord_640971 prefixEnd_640971 146278314930274191873215 := by
  unfold tailWord_640971
  simp only [CollatzResearch.WordTrace]
  refine ⟨23378132960879010976626767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15585421973919340651084511 23378132960879010976626767)
  ·
    refine ⟨35067199441318516464940151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23378132960879010976626767 35067199441318516464940151)
    ·
      refine ⟨52600799161977774697410227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35067199441318516464940151 52600799161977774697410227)
      ·
        refine ⟨78901198742966662046115341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52600799161977774697410227 78901198742966662046115341)
        ·
          refine ⟨29587949528612498267293253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78901198742966662046115341 29587949528612498267293253)
          ·
            refine ⟨5547740536614843425117485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29587949528612498267293253 5547740536614843425117485)
            ·
              refine ⟨2080402701230566284419057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5547740536614843425117485 2080402701230566284419057)
              ·
                refine ⟨1560302025922924713314293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080402701230566284419057 1560302025922924713314293)
                ·
                  refine ⟨146278314930274191873215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1560302025922924713314293 146278314930274191873215)
                  ·
                    rfl

theorem cell21_640971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_640971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640971 prefixEnd_640971 := by exact prefixLift 640971
  have htrace : WordTrace (prefixWord ++ tailWord_640971) baseStart_640971 baseEnd_640971 := by
    simpa [prefixWord, tailWord_640971, baseEnd_640971] using wordTrace_append hprefix tailTrace_640971
  have hstable : (prefixWord ++ tailWord_640971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640971).length < 2 ^ (prefixWord ++ tailWord_640971).sum := by decide
  have hdescent : baseEnd_640971 < baseStart_640971 := by decide
  rcases family_descends (prefixWord ++ tailWord_640971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640994 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 4]
def baseStart_640994 : Nat := 118140960795 + 640994 * 2 ^ 59
def prefixEnd_640994 : Nat := 4983230072969 + 3 ^ 40 * 640994 * 2
def baseEnd_640994 : Nat := 146283563843631262989835

theorem tailTrace_640994 : CollatzResearch.WordTrace tailWord_640994 prefixEnd_640994 146283563843631262989835 := by
  unfold tailWord_640994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5844742959948921476178509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15585981226530457269809357 5844742959948921476178509)
  ·
    refine ⟨2191778609980845553566941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5844742959948921476178509 2191778609980845553566941)
    ·
      refine ⟨821916978742817082587603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2191778609980845553566941 821916978742817082587603)
      ·
        refine ⟨1232875468114225623881405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 821916978742817082587603 1232875468114225623881405)
        ·
          refine ⟨462328300542834608955527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1232875468114225623881405 462328300542834608955527)
          ·
            refine ⟨693492450814251913433291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462328300542834608955527 693492450814251913433291)
            ·
              refine ⟨1040238676221377870149937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693492450814251913433291 1040238676221377870149937)
              ·
                refine ⟨780179007166033402612453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040238676221377870149937 780179007166033402612453)
                ·
                  refine ⟨146283563843631262989835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 780179007166033402612453 146283563843631262989835)
                  ·
                    rfl

theorem cell21_640994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_640994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_640994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_640994 prefixEnd_640994 := by exact prefixLift 640994
  have htrace : WordTrace (prefixWord ++ tailWord_640994) baseStart_640994 baseEnd_640994 := by
    simpa [prefixWord, tailWord_640994, baseEnd_640994] using wordTrace_append hprefix tailTrace_640994
  have hstable : (prefixWord ++ tailWord_640994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640994).length < 2 ^ (prefixWord ++ tailWord_640994).sum := by decide
  have hdescent : baseEnd_640994 < baseStart_640994 := by decide
  rcases family_descends (prefixWord ++ tailWord_640994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641002 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_641002 : Nat := 118140960795 + 641002 * 2 ^ 59
def prefixEnd_641002 : Nat := 4983230072969 + 3 ^ 40 * 641002 * 2
def baseEnd_641002 : Nat := 146285389552625026856485

theorem tailTrace_641002 : CollatzResearch.WordTrace tailWord_641002 prefixEnd_641002 146285389552625026856485 := by
  unfold tailWord_641002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5844815905941675817751315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15586175749177802180670173 5844815905941675817751315)
  ·
    refine ⟨8767223858912513726626973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5844815905941675817751315 8767223858912513726626973)
    ·
      refine ⟨3287708947092192647485115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8767223858912513726626973 3287708947092192647485115)
      ·
        refine ⟨4931563420638288971227673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3287708947092192647485115 4931563420638288971227673)
        ·
          refine ⟨3698672565478716728420755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4931563420638288971227673 3698672565478716728420755)
          ·
            refine ⟨5548008848218075092631133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698672565478716728420755 5548008848218075092631133)
            ·
              refine ⟨2080503318081778159736675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5548008848218075092631133 2080503318081778159736675)
              ·
                refine ⟨3120754977122667239605013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080503318081778159736675 3120754977122667239605013)
                ·
                  refine ⟨146285389552625026856485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3120754977122667239605013 146285389552625026856485)
                  ·
                    rfl

theorem cell21_641002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_641002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641002 prefixEnd_641002 := by exact prefixLift 641002
  have htrace : WordTrace (prefixWord ++ tailWord_641002) baseStart_641002 baseEnd_641002 := by
    simpa [prefixWord, tailWord_641002, baseEnd_641002] using wordTrace_append hprefix tailTrace_641002
  have hstable : (prefixWord ++ tailWord_641002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641002).length < 2 ^ (prefixWord ++ tailWord_641002).sum := by decide
  have hdescent : baseEnd_641002 < baseStart_641002 := by decide
  rcases family_descends (prefixWord ++ tailWord_641002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641157 : List Nat := [1, 3, 1, 1, 5, 2, 2, 3, 3]
def baseStart_641157 : Nat := 118140960795 + 641157 * 2 ^ 59
def prefixEnd_641157 : Nat := 4983230072969 + 3 ^ 40 * 641157 * 2
def baseEnd_641157 : Nat := 146320762664379201772835

theorem tailTrace_641157 : CollatzResearch.WordTrace tailWord_641157 prefixEnd_641157 146320762664379201772835 := by
  unfold tailWord_641157
  simp only [CollatzResearch.WordTrace]
  refine ⟨23384916938205164742897725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15589944625470109828598483 23384916938205164742897725)
  ·
    refine ⟨8769343851826936778586647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23384916938205164742897725 8769343851826936778586647)
    ·
      refine ⟨13154015777740405167879971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8769343851826936778586647 13154015777740405167879971)
      ·
        refine ⟨19731023666610607751819957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13154015777740405167879971 19731023666610607751819957)
        ·
          refine ⟨1849783468744744476733121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19731023666610607751819957 1849783468744744476733121)
          ·
            refine ⟨1387337601558558357549841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1849783468744744476733121 1387337601558558357549841)
            ·
              refine ⟨1040503201168918768162381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387337601558558357549841 1040503201168918768162381)
              ·
                refine ⟨390188700438344538060893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1040503201168918768162381 390188700438344538060893)
                ·
                  refine ⟨146320762664379201772835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390188700438344538060893 146320762664379201772835)
                  ·
                    rfl

theorem cell21_641157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_641157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641157 prefixEnd_641157 := by exact prefixLift 641157
  have htrace : WordTrace (prefixWord ++ tailWord_641157) baseStart_641157 baseEnd_641157 := by
    simpa [prefixWord, tailWord_641157, baseEnd_641157] using wordTrace_append hprefix tailTrace_641157
  have hstable : (prefixWord ++ tailWord_641157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641157).length < 2 ^ (prefixWord ++ tailWord_641157).sum := by decide
  have hdescent : baseEnd_641157 < baseStart_641157 := by decide
  rcases family_descends (prefixWord ++ tailWord_641157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641188 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 4]
def baseStart_641188 : Nat := 118140960795 + 641188 * 2 ^ 59
def prefixEnd_641188 : Nat := 4983230072969 + 3 ^ 40 * 641188 * 2
def baseEnd_641188 : Nat := 146327837286730036756105

theorem tailTrace_641188 : CollatzResearch.WordTrace tailWord_641188 prefixEnd_641188 146327837286730036756105 := by
  unfold tailWord_641188
  simp only [CollatzResearch.WordTrace]
  refine ⟨11693023800546428518638109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15590698400728571358184145 11693023800546428518638109)
  ·
    refine ⟨4384883925204910694489291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11693023800546428518638109 4384883925204910694489291)
    ·
      refine ⟨6577325887807366041733937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4384883925204910694489291 6577325887807366041733937)
      ·
        refine ⟨4932994415855524531300453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6577325887807366041733937 4932994415855524531300453)
        ·
          refine ⟨924936452972910849618835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4932994415855524531300453 924936452972910849618835)
          ·
            refine ⟨1387404679459366274428253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924936452972910849618835 1387404679459366274428253)
            ·
              refine ⟨520276754797262352910595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1387404679459366274428253 520276754797262352910595)
              ·
                refine ⟨780415132195893529365893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520276754797262352910595 780415132195893529365893)
                ·
                  refine ⟨146327837286730036756105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 780415132195893529365893 146327837286730036756105)
                  ·
                    rfl

theorem cell21_641188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_641188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641188 prefixEnd_641188 := by exact prefixLift 641188
  have htrace : WordTrace (prefixWord ++ tailWord_641188) baseStart_641188 baseEnd_641188 := by
    simpa [prefixWord, tailWord_641188, baseEnd_641188] using wordTrace_append hprefix tailTrace_641188
  have hstable : (prefixWord ++ tailWord_641188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641188).length < 2 ^ (prefixWord ++ tailWord_641188).sum := by decide
  have hdescent : baseEnd_641188 < baseStart_641188 := by decide
  rcases family_descends (prefixWord ++ tailWord_641188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641230 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_641230 : Nat := 118140960795 + 641230 * 2 ^ 59
def prefixEnd_641230 : Nat := 4983230072969 + 3 ^ 40 * 641230 * 2
def baseEnd_641230 : Nat := 146337422258947297056019

theorem tailTrace_641230 : CollatzResearch.WordTrace tailWord_641230 prefixEnd_641230 146337422258947297056019 := by
  unfold tailWord_641230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923447433367587276288143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15591719644627132140203429 2923447433367587276288143)
  ·
    refine ⟨4385171150051380914432215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2923447433367587276288143 4385171150051380914432215)
    ·
      refine ⟨6577756725077071371648323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4385171150051380914432215 6577756725077071371648323)
      ·
        refine ⟨9866635087615607057472485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6577756725077071371648323 9866635087615607057472485)
        ·
          refine ⟨1849994078927926323276091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9866635087615607057472485 1849994078927926323276091)
          ·
            refine ⟨2774991118391889484914137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849994078927926323276091 2774991118391889484914137)
            ·
              refine ⟨2081243338793917113685603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2774991118391889484914137 2081243338793917113685603)
              ·
                refine ⟨3121865008190875670528405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081243338793917113685603 3121865008190875670528405)
                ·
                  refine ⟨146337422258947297056019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3121865008190875670528405 146337422258947297056019)
                  ·
                    rfl

theorem cell21_641230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_641230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641230 prefixEnd_641230 := by exact prefixLift 641230
  have htrace : WordTrace (prefixWord ++ tailWord_641230) baseStart_641230 baseEnd_641230 := by
    simpa [prefixWord, tailWord_641230, baseEnd_641230] using wordTrace_append hprefix tailTrace_641230
  have hstable : (prefixWord ++ tailWord_641230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641230).length < 2 ^ (prefixWord ++ tailWord_641230).sum := by decide
  have hdescent : baseEnd_641230 < baseStart_641230 := by decide
  rcases family_descends (prefixWord ++ tailWord_641230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641292 : List Nat := [2, 2, 1, 2, 2, 2, 3, 4, 3]
def baseStart_641292 : Nat := 118140960795 + 641292 * 2 ^ 59
def prefixEnd_641292 : Nat := 4983230072969 + 3 ^ 40 * 641292 * 2
def baseEnd_641292 : Nat := 146351571503648967022559

theorem tailTrace_641292 : CollatzResearch.WordTrace tailWord_641292 prefixEnd_641292 146351571503648967022559 := by
  unfold tailWord_641292
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694920396358041399531065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15593227195144055199374753 11694920396358041399531065)
  ·
    refine ⟨8771190297268531049648299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11694920396358041399531065 8771190297268531049648299)
    ·
      refine ⟨13156785445902796574472449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8771190297268531049648299 13156785445902796574472449)
      ·
        refine ⟨9867589084427097430854337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13156785445902796574472449 9867589084427097430854337)
        ·
          refine ⟨7400691813320323073140753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9867589084427097430854337 7400691813320323073140753)
          ·
            refine ⟨5550518859990242304855565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7400691813320323073140753 5550518859990242304855565)
            ·
              refine ⟨2081444572496340864320837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5550518859990242304855565 2081444572496340864320837)
              ·
                refine ⟨390270857343063912060157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2081444572496340864320837 390270857343063912060157)
                ·
                  refine ⟨146351571503648967022559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390270857343063912060157 146351571503648967022559)
                  ·
                    rfl

theorem cell21_641292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_641292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641292 prefixEnd_641292 := by exact prefixLift 641292
  have htrace : WordTrace (prefixWord ++ tailWord_641292) baseStart_641292 baseEnd_641292 := by
    simpa [prefixWord, tailWord_641292, baseEnd_641292] using wordTrace_append hprefix tailTrace_641292
  have hstable : (prefixWord ++ tailWord_641292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641292).length < 2 ^ (prefixWord ++ tailWord_641292).sum := by decide
  have hdescent : baseEnd_641292 < baseStart_641292 := by decide
  rcases family_descends (prefixWord ++ tailWord_641292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641351 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 5]
def baseStart_641351 : Nat := 118140960795 + 641351 * 2 ^ 59
def prefixEnd_641351 : Nat := 4983230072969 + 3 ^ 40 * 641351 * 2
def baseEnd_641351 : Nat := 146365036107477975539105

theorem tailTrace_641351 : CollatzResearch.WordTrace tailWord_641351 prefixEnd_641351 146365036107477975539105 := by
  unfold tailWord_641351
  simp only [CollatzResearch.WordTrace]
  refine ⟨23391992699502335875459907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15594661799668223916973271 23391992699502335875459907)
  ·
    refine ⟨35087989049253503813189861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23391992699502335875459907 35087989049253503813189861)
    ·
      refine ⟨6578997946735031964973099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35087989049253503813189861 6578997946735031964973099)
      ·
        refine ⟨9868496920102547947459649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6578997946735031964973099 9868496920102547947459649)
        ·
          refine ⟨7401372690076910960594737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9868496920102547947459649 7401372690076910960594737)
          ·
            refine ⟨5551029517557683220446053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7401372690076910960594737 5551029517557683220446053)
            ·
              refine ⟨1040818034542065603833635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5551029517557683220446053 1040818034542065603833635)
              ·
                refine ⟨1561227051813098405750453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040818034542065603833635 1561227051813098405750453)
                ·
                  refine ⟨146365036107477975539105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1561227051813098405750453 146365036107477975539105)
                  ·
                    rfl

theorem cell21_641351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 5].length) (baseStart_641351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641351 prefixEnd_641351 := by exact prefixLift 641351
  have htrace : WordTrace (prefixWord ++ tailWord_641351) baseStart_641351 baseEnd_641351 := by
    simpa [prefixWord, tailWord_641351, baseEnd_641351] using wordTrace_append hprefix tailTrace_641351
  have hstable : (prefixWord ++ tailWord_641351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641351).length < 2 ^ (prefixWord ++ tailWord_641351).sum := by decide
  have hdescent : baseEnd_641351 < baseStart_641351 := by decide
  rcases family_descends (prefixWord ++ tailWord_641351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641458 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_641458 : Nat := 118140960795 + 641458 * 2 ^ 59
def prefixEnd_641458 : Nat := 4983230072969 + 3 ^ 40 * 641458 * 2
def baseEnd_641458 : Nat := 146389454965269567255553

theorem tailTrace_641458 : CollatzResearch.WordTrace tailWord_641458 prefixEnd_641458 146389454965269567255553 := by
  unfold tailWord_641458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5848973827528673287401257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15597263540076462099736685 5848973827528673287401257)
  ·
    refine ⟨4386730370646504965550943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5848973827528673287401257 4386730370646504965550943)
    ·
      refine ⟨6580095555969757448326415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4386730370646504965550943 6580095555969757448326415)
      ·
        refine ⟨9870143333954636172489623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6580095555969757448326415 9870143333954636172489623)
        ·
          refine ⟨14805215000931954258734435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9870143333954636172489623 14805215000931954258734435)
          ·
            refine ⟨22207822501397931388101653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14805215000931954258734435 22207822501397931388101653)
            ·
              refine ⟨1040991679753028033817265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22207822501397931388101653 1040991679753028033817265)
              ·
                refine ⟨780743759814771025362949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040991679753028033817265 780743759814771025362949)
                ·
                  refine ⟨146389454965269567255553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 780743759814771025362949 146389454965269567255553)
                  ·
                    rfl

theorem cell21_641458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_641458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641458 prefixEnd_641458 := by exact prefixLift 641458
  have htrace : WordTrace (prefixWord ++ tailWord_641458) baseStart_641458 baseEnd_641458 := by
    simpa [prefixWord, tailWord_641458, baseEnd_641458] using wordTrace_append hprefix tailTrace_641458
  have hstable : (prefixWord ++ tailWord_641458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641458).length < 2 ^ (prefixWord ++ tailWord_641458).sum := by decide
  have hdescent : baseEnd_641458 < baseStart_641458 := by decide
  rcases family_descends (prefixWord ++ tailWord_641458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641461 : List Nat := [1, 3, 3, 2, 3, 1, 1, 4, 3]
def baseStart_641461 : Nat := 118140960795 + 641461 * 2 ^ 59
def prefixEnd_641461 : Nat := 4983230072969 + 3 ^ 40 * 641461 * 2
def baseEnd_641461 : Nat := 146390139606142228705547

theorem tailTrace_641461 : CollatzResearch.WordTrace tailWord_641461 prefixEnd_641461 146390139606142228705547 := by
  unfold tailWord_641461
  simp only [CollatzResearch.WordTrace]
  refine ⟨23396004729103824661964237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15597336486069216441309491 23396004729103824661964237)
  ·
    refine ⟨8773501773413934248236589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23396004729103824661964237 8773501773413934248236589)
    ·
      refine ⟨3290063165030225343088721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8773501773413934248236589 3290063165030225343088721)
      ·
        refine ⟨2467547373772669007316541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3290063165030225343088721 2467547373772669007316541)
        ·
          refine ⟨925330265164750877743703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2467547373772669007316541 925330265164750877743703)
          ·
            refine ⟨1387995397747126316615555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925330265164750877743703 1387995397747126316615555)
            ·
              refine ⟨2081993096620689474923333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387995397747126316615555 2081993096620689474923333)
              ·
                refine ⟨390373705616379276548125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2081993096620689474923333 390373705616379276548125)
                ·
                  refine ⟨146390139606142228705547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390373705616379276548125 146390139606142228705547)
                  ·
                    rfl

theorem cell21_641461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_641461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641461 prefixEnd_641461 := by exact prefixLift 641461
  have htrace : WordTrace (prefixWord ++ tailWord_641461) baseStart_641461 baseEnd_641461 := by
    simpa [prefixWord, tailWord_641461, baseEnd_641461] using wordTrace_append hprefix tailTrace_641461
  have hstable : (prefixWord ++ tailWord_641461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641461).length < 2 ^ (prefixWord ++ tailWord_641461).sum := by decide
  have hdescent : baseEnd_641461 < baseStart_641461 := by decide
  rcases family_descends (prefixWord ++ tailWord_641461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641506 : List Nat := [3, 3, 3, 2, 1, 1, 8]
def baseStart_641506 : Nat := 118140960795 + 641506 * 2 ^ 59
def prefixEnd_641506 : Nat := 4983230072969 + 3 ^ 40 * 641506 * 2
def baseEnd_641506 : Nat := 16266712135470238939495

theorem tailTrace_641506 : CollatzResearch.WordTrace tailWord_641506 prefixEnd_641506 16266712135470238939495 := by
  unfold tailWord_641506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849411503485199336838093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15598430675960531564901581 5849411503485199336838093)
  ·
    refine ⟨2193529313806949751314285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5849411503485199336838093 2193529313806949751314285)
    ·
      refine ⟨822573492677606156742857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2193529313806949751314285 822573492677606156742857)
      ·
        refine ⟨616930119508204617557143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 822573492677606156742857 616930119508204617557143)
        ·
          refine ⟨925395179262306926335715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616930119508204617557143 925395179262306926335715)
          ·
            refine ⟨1388092768893460389503573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925395179262306926335715 1388092768893460389503573)
            ·
              refine ⟨16266712135470238939495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1388092768893460389503573 16266712135470238939495)
              ·
                rfl

theorem cell21_641506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 8].length) (baseStart_641506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641506 prefixEnd_641506 := by exact prefixLift 641506
  have htrace : WordTrace (prefixWord ++ tailWord_641506) baseStart_641506 baseEnd_641506 := by
    simpa [prefixWord, tailWord_641506, baseEnd_641506] using wordTrace_append hprefix tailTrace_641506
  have hstable : (prefixWord ++ tailWord_641506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641506).length < 2 ^ (prefixWord ++ tailWord_641506).sum := by decide
  have hdescent : baseEnd_641506 < baseStart_641506 := by decide
  rcases family_descends (prefixWord ++ tailWord_641506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641548 : List Nat := [2, 2, 1, 2, 4, 2, 1, 7]
def baseStart_641548 : Nat := 118140960795 + 641548 * 2 ^ 59
def prefixEnd_641548 : Nat := 4983230072969 + 3 ^ 40 * 641548 * 2
def baseEnd_641548 : Nat := 48803331397149803585123

theorem tailTrace_641548 : CollatzResearch.WordTrace tailWord_641548 prefixEnd_641548 48803331397149803585123 := by
  unfold tailWord_641548
  simp only [CollatzResearch.WordTrace]
  refine ⟨11699588939894319260190649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15599451919859092346920865 11699588939894319260190649)
  ·
    refine ⟨8774691704920739445142987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11699588939894319260190649 8774691704920739445142987)
    ·
      refine ⟨13162037557381109167714481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8774691704920739445142987 13162037557381109167714481)
      ·
        refine ⟨9871528168035831875785861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13162037557381109167714481 9871528168035831875785861)
        ·
          refine ⟨1850911531506718476709849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9871528168035831875785861 1850911531506718476709849)
          ·
            refine ⟨1388183648630038857532387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1850911531506718476709849 1388183648630038857532387)
            ·
              refine ⟨2082275472945058286298581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388183648630038857532387 2082275472945058286298581)
              ·
                refine ⟨48803331397149803585123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2082275472945058286298581 48803331397149803585123)
                ·
                  rfl

theorem cell21_641548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_641548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641548 prefixEnd_641548 := by exact prefixLift 641548
  have htrace : WordTrace (prefixWord ++ tailWord_641548) baseStart_641548 baseEnd_641548 := by
    simpa [prefixWord, tailWord_641548, baseEnd_641548] using wordTrace_append hprefix tailTrace_641548
  have hstable : (prefixWord ++ tailWord_641548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641548).length < 2 ^ (prefixWord ++ tailWord_641548).sum := by decide
  have hdescent : baseEnd_641548 < baseStart_641548 := by decide
  rcases family_descends (prefixWord ++ tailWord_641548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641562 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_641562 : Nat := 118140960795 + 641562 * 2 ^ 59
def prefixEnd_641562 : Nat := 4983230072969 + 3 ^ 40 * 641562 * 2
def baseEnd_641562 : Nat := 146413189182188497522007

theorem tailTrace_641562 : CollatzResearch.WordTrace tailWord_641562 prefixEnd_641562 146413189182188497522007 := by
  unfold tailWord_641562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849922125434479727847735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15599792334491945940927293 5849922125434479727847735)
  ·
    refine ⟨8774883188151719591771603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5849922125434479727847735 8774883188151719591771603)
    ·
      refine ⟨13162324782227579387657405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8774883188151719591771603 13162324782227579387657405)
      ·
        refine ⟨4935871793335342270371527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13162324782227579387657405 4935871793335342270371527)
        ·
          refine ⟨7403807690003013405557291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4935871793335342270371527 7403807690003013405557291)
          ·
            refine ⟨11105711535004520108335937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7403807690003013405557291 11105711535004520108335937)
            ·
              refine ⟨8329283651253390081251953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11105711535004520108335937 8329283651253390081251953)
              ·
                refine ⟨6246962738440042560938965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8329283651253390081251953 6246962738440042560938965)
                ·
                  refine ⟨146413189182188497522007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6246962738440042560938965 146413189182188497522007)
                  ·
                    rfl

theorem cell21_641562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_641562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641562 prefixEnd_641562 := by exact prefixLift 641562
  have htrace : WordTrace (prefixWord ++ tailWord_641562) baseStart_641562 baseEnd_641562 := by
    simpa [prefixWord, tailWord_641562, baseEnd_641562] using wordTrace_append hprefix tailTrace_641562
  have hstable : (prefixWord ++ tailWord_641562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641562).length < 2 ^ (prefixWord ++ tailWord_641562).sum := by decide
  have hdescent : baseEnd_641562 < baseStart_641562 := by decide
  rcases family_descends (prefixWord ++ tailWord_641562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641579 : List Nat := [1, 1, 1, 1, 2, 1, 3, 8, 3]
def baseStart_641579 : Nat := 118140960795 + 641579 * 2 ^ 59
def prefixEnd_641579 : Nat := 4983230072969 + 3 ^ 40 * 641579 * 2
def baseEnd_641579 : Nat := 146417068813800245738639

theorem tailTrace_641579 : CollatzResearch.WordTrace tailWord_641579 prefixEnd_641579 146417068813800245738639 := by
  unfold tailWord_641579
  simp only [CollatzResearch.WordTrace]
  refine ⟨23400308542676330814759791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15600205695117553876506527 23400308542676330814759791)
  ·
    refine ⟨35100462814014496222139687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23400308542676330814759791 35100462814014496222139687)
    ·
      refine ⟨52650694221021744333209531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35100462814014496222139687 52650694221021744333209531)
      ·
        refine ⟨78976041331532616499814297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52650694221021744333209531 78976041331532616499814297)
        ·
          refine ⟨59232030998649462374860723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78976041331532616499814297 59232030998649462374860723)
          ·
            refine ⟨88848046497974193562291085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59232030998649462374860723 88848046497974193562291085)
            ·
              refine ⟨33318017436740322585859157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88848046497974193562291085 33318017436740322585859157)
              ·
                refine ⟨390445516836800655303037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 33318017436740322585859157 390445516836800655303037)
                ·
                  refine ⟨146417068813800245738639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390445516836800655303037 146417068813800245738639)
                  ·
                    rfl

theorem cell21_641579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 3].length) (baseStart_641579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641579 prefixEnd_641579 := by exact prefixLift 641579
  have htrace : WordTrace (prefixWord ++ tailWord_641579) baseStart_641579 baseEnd_641579 := by
    simpa [prefixWord, tailWord_641579, baseEnd_641579] using wordTrace_append hprefix tailTrace_641579
  have hstable : (prefixWord ++ tailWord_641579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641579).length < 2 ^ (prefixWord ++ tailWord_641579).sum := by decide
  have hdescent : baseEnd_641579 < baseStart_641579 := by decide
  rcases family_descends (prefixWord ++ tailWord_641579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641717 : List Nat := [1, 3, 3, 3, 1, 1, 4, 5]
def baseStart_641717 : Nat := 118140960795 + 641717 * 2 ^ 59
def prefixEnd_641717 : Nat := 4983230072969 + 3 ^ 40 * 641717 * 2
def baseEnd_641717 : Nat := 48816187431314224146119

theorem tailTrace_641717 : CollatzResearch.WordTrace tailWord_641717 prefixEnd_641717 48816187431314224146119 := by
  unfold tailWord_641717
  simp only [CollatzResearch.WordTrace]
  refine ⟨23405341816176380383283405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15603561210784253588855603 23405341816176380383283405)
  ·
    refine ⟨8777003181066142643731277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23405341816176380383283405 8777003181066142643731277)
    ·
      refine ⟨3291376192899803491399229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8777003181066142643731277 3291376192899803491399229)
      ·
        refine ⟨1234266072337426309274711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3291376192899803491399229 1234266072337426309274711)
        ·
          refine ⟨1851399108506139463912067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234266072337426309274711 1851399108506139463912067)
          ·
            refine ⟨2777098662759209195868101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851399108506139463912067 2777098662759209195868101)
            ·
              refine ⟨520705999267351724225269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2777098662759209195868101 520705999267351724225269)
              ·
                refine ⟨48816187431314224146119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 520705999267351724225269 48816187431314224146119)
                ·
                  rfl

theorem cell21_641717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 5].length) (baseStart_641717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641717 prefixEnd_641717 := by exact prefixLift 641717
  have htrace : WordTrace (prefixWord ++ tailWord_641717) baseStart_641717 baseEnd_641717 := by
    simpa [prefixWord, tailWord_641717, baseEnd_641717] using wordTrace_append hprefix tailTrace_641717
  have hstable : (prefixWord ++ tailWord_641717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641717).length < 2 ^ (prefixWord ++ tailWord_641717).sum := by decide
  have hdescent : baseEnd_641717 < baseStart_641717 := by decide
  rcases family_descends (prefixWord ++ tailWord_641717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641745 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 4]
def baseStart_641745 : Nat := 118140960795 + 641745 * 2 ^ 59
def prefixEnd_641745 : Nat := 4983230072969 + 3 ^ 40 * 641745 * 2
def baseEnd_641745 : Nat := 146454952275420845971633

theorem tailTrace_641745 : CollatzResearch.WordTrace tailWord_641745 prefixEnd_641745 146454952275420845971633 := by
  unfold tailWord_641745
  simp only [CollatzResearch.WordTrace]
  refine ⟨23406363060074941165302689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15604242040049960776868459 23406363060074941165302689)
  ·
    refine ⟨17554772295056205873977017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23406363060074941165302689 17554772295056205873977017)
    ·
      refine ⟨13166079221292154405482763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17554772295056205873977017 13166079221292154405482763)
      ·
        refine ⟨19749118831938231608224145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13166079221292154405482763 19749118831938231608224145)
        ·
          refine ⟨14811839123953673706168109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19749118831938231608224145 14811839123953673706168109)
          ·
            refine ⟨5554439671482627639813041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14811839123953673706168109 5554439671482627639813041)
            ·
              refine ⟨4165829753611970729859781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5554439671482627639813041 4165829753611970729859781)
              ·
                refine ⟨781093078802244511848709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4165829753611970729859781 781093078802244511848709)
                ·
                  refine ⟨146454952275420845971633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 781093078802244511848709 146454952275420845971633)
                  ·
                    rfl

theorem cell21_641745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_641745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641745 prefixEnd_641745 := by exact prefixLift 641745
  have htrace : WordTrace (prefixWord ++ tailWord_641745) baseStart_641745 baseEnd_641745 := by
    simpa [prefixWord, tailWord_641745, baseEnd_641745] using wordTrace_append hprefix tailTrace_641745
  have hstable : (prefixWord ++ tailWord_641745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641745).length < 2 ^ (prefixWord ++ tailWord_641745).sum := by decide
  have hdescent : baseEnd_641745 < baseStart_641745 := by decide
  rcases family_descends (prefixWord ++ tailWord_641745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641759 : List Nat := [1, 1, 2, 3, 2, 3, 1, 8]
def baseStart_641759 : Nat := 118140960795 + 641759 * 2 ^ 59
def prefixEnd_641759 : Nat := 4983230072969 + 3 ^ 40 * 641759 * 2
def baseEnd_641759 : Nat := 48819382422053310912757

theorem tailTrace_641759 : CollatzResearch.WordTrace tailWord_641759 prefixEnd_641759 48819382422053310912757 := by
  unfold tailWord_641759
  simp only [CollatzResearch.WordTrace]
  refine ⟨23406873682024221556312331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15604582454682814370874887 23406873682024221556312331)
  ·
    refine ⟨35110310523036332334468497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23406873682024221556312331 35110310523036332334468497)
    ·
      refine ⟨26332732892277249250851373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35110310523036332334468497 26332732892277249250851373)
      ·
        refine ⟨9874774834603968469069265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26332732892277249250851373 9874774834603968469069265)
        ·
          refine ⟨7406081125952976351801949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9874774834603968469069265 7406081125952976351801949)
          ·
            refine ⟨2777280422232366131925731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7406081125952976351801949 2777280422232366131925731)
            ·
              refine ⟨4165920633348549197888597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777280422232366131925731 4165920633348549197888597)
              ·
                refine ⟨48819382422053310912757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4165920633348549197888597 48819382422053310912757)
                ·
                  rfl

theorem cell21_641759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 8].length) (baseStart_641759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641759 prefixEnd_641759 := by exact prefixLift 641759
  have htrace : WordTrace (prefixWord ++ tailWord_641759) baseStart_641759 baseEnd_641759 := by
    simpa [prefixWord, tailWord_641759, baseEnd_641759] using wordTrace_append hprefix tailTrace_641759
  have hstable : (prefixWord ++ tailWord_641759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641759).length < 2 ^ (prefixWord ++ tailWord_641759).sum := by decide
  have hdescent : baseEnd_641759 < baseStart_641759 := by decide
  rcases family_descends (prefixWord ++ tailWord_641759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641807 : List Nat := [1, 1, 2, 1, 1, 1, 7, 4, 3]
def baseStart_641807 : Nat := 118140960795 + 641807 * 2 ^ 59
def prefixEnd_641807 : Nat := 4983230072969 + 3 ^ 40 * 641807 * 2
def baseEnd_641807 : Nat := 146469101520122515938173

theorem tailTrace_641807 : CollatzResearch.WordTrace tailWord_641807 prefixEnd_641807 146469101520122515938173 := by
  unfold tailWord_641807
  simp only [CollatzResearch.WordTrace]
  refine ⟨23408624385850325754059675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15605749590566883836039783 23408624385850325754059675)
  ·
    refine ⟨35112936578775488631089513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23408624385850325754059675 35112936578775488631089513)
    ·
      refine ⟨26334702434081616473317135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35112936578775488631089513 26334702434081616473317135)
      ·
        refine ⟨39502053651122424709975703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26334702434081616473317135 39502053651122424709975703)
        ·
          refine ⟨59253080476683637064963555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39502053651122424709975703 59253080476683637064963555)
          ·
            refine ⟨88879620715025455597445333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59253080476683637064963555 88879620715025455597445333)
            ·
              refine ⟨2083116110508409115565125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 88879620715025455597445333 2083116110508409115565125)
              ·
                refine ⟨390584270720326709168461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2083116110508409115565125 390584270720326709168461)
                ·
                  refine ⟨146469101520122515938173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390584270720326709168461 146469101520122515938173)
                  ·
                    rfl

theorem cell21_641807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 3].length) (baseStart_641807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641807 prefixEnd_641807 := by exact prefixLift 641807
  have htrace : WordTrace (prefixWord ++ tailWord_641807) baseStart_641807 baseEnd_641807 := by
    simpa [prefixWord, tailWord_641807, baseEnd_641807] using wordTrace_append hprefix tailTrace_641807
  have hstable : (prefixWord ++ tailWord_641807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641807).length < 2 ^ (prefixWord ++ tailWord_641807).sum := by decide
  have hdescent : baseEnd_641807 < baseStart_641807 := by decide
  rcases family_descends (prefixWord ++ tailWord_641807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641810 : List Nat := [3, 2, 4, 1, 2, 2, 1, 6]
def baseStart_641810 : Nat := 118140960795 + 641810 * 2 ^ 59
def prefixEnd_641810 : Nat := 4983230072969 + 3 ^ 40 * 641810 * 2
def baseEnd_641810 : Nat := 48823262053665059129389

theorem tailTrace_641810 : CollatzResearch.WordTrace tailWord_641810 prefixEnd_641810 48823262053665059129389 := by
  unfold tailWord_641810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5852183451209864316604721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15605822536559638177612589 5852183451209864316604721)
  ·
    refine ⟨4389137588407398237453541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5852183451209864316604721 4389137588407398237453541)
    ·
      refine ⟨822963297826387169522539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4389137588407398237453541 822963297826387169522539)
      ·
        refine ⟨1234444946739580754283809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822963297826387169522539 1234444946739580754283809)
        ·
          refine ⟨925833710054685565712857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1234444946739580754283809 925833710054685565712857)
          ·
            refine ⟨694375282541014174284643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 925833710054685565712857 694375282541014174284643)
            ·
              refine ⟨1041562923811521261426965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694375282541014174284643 1041562923811521261426965)
              ·
                refine ⟨48823262053665059129389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1041562923811521261426965 48823262053665059129389)
                ·
                  rfl

theorem cell21_641810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_641810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641810 prefixEnd_641810 := by exact prefixLift 641810
  have htrace : WordTrace (prefixWord ++ tailWord_641810) baseStart_641810 baseEnd_641810 := by
    simpa [prefixWord, tailWord_641810, baseEnd_641810] using wordTrace_append hprefix tailTrace_641810
  have hstable : (prefixWord ++ tailWord_641810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641810).length < 2 ^ (prefixWord ++ tailWord_641810).sum := by decide
  have hdescent : baseEnd_641810 < baseStart_641810 := by decide
  rcases family_descends (prefixWord ++ tailWord_641810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641928 : List Nat := [2, 1, 3, 3, 2, 2, 2, 6]
def baseStart_641928 : Nat := 118140960795 + 641928 * 2 ^ 59
def prefixEnd_641928 : Nat := 4983230072969 + 3 ^ 40 * 641928 * 2
def baseEnd_641928 : Nat := 48832238456217731473753

theorem tailTrace_641928 : CollatzResearch.WordTrace tailWord_641928 prefixEnd_641928 48832238456217731473753 := by
  unfold tailWord_641928
  simp only [CollatzResearch.WordTrace]
  refine ⟨11706518809205981709607219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15608691745607975612809625 11706518809205981709607219)
  ·
    refine ⟨17559778213808972564410829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11706518809205981709607219 17559778213808972564410829)
    ·
      refine ⟨6584916830178364711654061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17559778213808972564410829 6584916830178364711654061)
      ·
        refine ⟨2469343811316886766870273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6584916830178364711654061 2469343811316886766870273)
        ·
          refine ⟨1852007858487665075152705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2469343811316886766870273 1852007858487665075152705)
          ·
            refine ⟨1389005893865748806364529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1852007858487665075152705 1389005893865748806364529)
            ·
              refine ⟨1041754420399311604773397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389005893865748806364529 1041754420399311604773397)
              ·
                refine ⟨48832238456217731473753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1041754420399311604773397 48832238456217731473753)
                ·
                  rfl

theorem cell21_641928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_641928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641928 prefixEnd_641928 := by exact prefixLift 641928
  have htrace : WordTrace (prefixWord ++ tailWord_641928) baseStart_641928 baseEnd_641928 := by
    simpa [prefixWord, tailWord_641928, baseEnd_641928] using wordTrace_append hprefix tailTrace_641928
  have hstable : (prefixWord ++ tailWord_641928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641928).length < 2 ^ (prefixWord ++ tailWord_641928).sum := by decide
  have hdescent : baseEnd_641928 < baseStart_641928 := by decide
  rcases family_descends (prefixWord ++ tailWord_641928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641976 : List Nat := [2, 1, 2, 1, 2, 4, 4, 2, 3]
def baseStart_641976 : Nat := 118140960795 + 641976 * 2 ^ 59
def prefixEnd_641976 : Nat := 4983230072969 + 3 ^ 40 * 641976 * 2
def baseEnd_641976 : Nat := 146507669622615777621161

theorem tailTrace_641976 : CollatzResearch.WordTrace tailWord_641976 prefixEnd_641976 146507669622615777621161 := by
  unfold tailWord_641976
  simp only [CollatzResearch.WordTrace]
  refine ⟨11707394161119033808480891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15609858881492045077974521 11707394161119033808480891)
  ·
    refine ⟨17561091241678550712721337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11707394161119033808480891 17561091241678550712721337)
    ·
      refine ⟨13170818431258913034541003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17561091241678550712721337 13170818431258913034541003)
      ·
        refine ⟨19756227646888369551811505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13170818431258913034541003 19756227646888369551811505)
        ·
          refine ⟨14817170735166277163858629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19756227646888369551811505 14817170735166277163858629)
          ·
            refine ⟨2778219512843676968223493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14817170735166277163858629 2778219512843676968223493)
            ·
              refine ⟨520916158658189431541905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2778219512843676968223493 520916158658189431541905)
              ·
                refine ⟨390687118993642073656429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520916158658189431541905 390687118993642073656429)
                ·
                  refine ⟨146507669622615777621161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390687118993642073656429 146507669622615777621161)
                  ·
                    rfl

theorem cell21_641976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 3].length) (baseStart_641976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_641976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_641976 prefixEnd_641976 := by exact prefixLift 641976
  have htrace : WordTrace (prefixWord ++ tailWord_641976) baseStart_641976 baseEnd_641976 := by
    simpa [prefixWord, tailWord_641976, baseEnd_641976] using wordTrace_append hprefix tailTrace_641976
  have hstable : (prefixWord ++ tailWord_641976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641976).length < 2 ^ (prefixWord ++ tailWord_641976).sum := by decide
  have hdescent : baseEnd_641976 < baseStart_641976 := by decide
  rcases family_descends (prefixWord ++ tailWord_641976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642100 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 4]
def baseStart_642100 : Nat := 118140960795 + 642100 * 2 ^ 59
def prefixEnd_642100 : Nat := 4983230072969 + 3 ^ 40 * 642100 * 2
def baseEnd_642100 : Nat := 146535968112019117554241

theorem tailTrace_642100 : CollatzResearch.WordTrace tailWord_642100 prefixEnd_642100 146535968112019117554241 := by
  unfold tailWord_642100
  simp only [CollatzResearch.WordTrace]
  refine ⟨11709655486894418397237877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15612873982525891196317169 11709655486894418397237877)
  ·
    refine ⟨1097780201896351724741051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11709655486894418397237877 1097780201896351724741051)
    ·
      refine ⟨1646670302844527587111577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1097780201896351724741051 1646670302844527587111577)
      ·
        refine ⟨1235002727133395690333683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1646670302844527587111577 1235002727133395690333683)
        ·
          refine ⟨1852504090700093535500525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235002727133395690333683 1852504090700093535500525)
          ·
            refine ⟨694689034012535075812697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1852504090700093535500525 694689034012535075812697)
            ·
              refine ⟨521016775509401306859523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694689034012535075812697 521016775509401306859523)
              ·
                refine ⟨781525163264101960289285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521016775509401306859523 781525163264101960289285)
                ·
                  refine ⟨146535968112019117554241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 781525163264101960289285 146535968112019117554241)
                  ·
                    rfl

theorem cell21_642100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_642100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642100 prefixEnd_642100 := by exact prefixLift 642100
  have htrace : WordTrace (prefixWord ++ tailWord_642100) baseStart_642100 baseEnd_642100 := by
    simpa [prefixWord, tailWord_642100, baseEnd_642100] using wordTrace_append hprefix tailTrace_642100
  have hstable : (prefixWord ++ tailWord_642100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642100).length < 2 ^ (prefixWord ++ tailWord_642100).sum := by decide
  have hdescent : baseEnd_642100 < baseStart_642100 := by decide
  rcases family_descends (prefixWord ++ tailWord_642100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642356 : List Nat := [2, 5, 1, 1, 1, 1, 4, 3, 3]
def baseStart_642356 : Nat := 118140960795 + 642356 * 2 ^ 59
def prefixEnd_642356 : Nat := 4983230072969 + 3 ^ 40 * 642356 * 2
def baseEnd_642356 : Nat := 146594390799819561287051

theorem tailTrace_642356 : CollatzResearch.WordTrace tailWord_642356 prefixEnd_642356 146594390799819561287051 := by
  unfold tailWord_642356
  simp only [CollatzResearch.WordTrace]
  refine ⟨11714324030430696257897461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15619098707240928343863281 11714324030430696257897461)
  ·
    refine ⟨1098217877852877774177887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11714324030430696257897461 1098217877852877774177887)
    ·
      refine ⟨1647326816779316661266831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1098217877852877774177887 1647326816779316661266831)
      ·
        refine ⟨2470990225168974991900247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1647326816779316661266831 2470990225168974991900247)
        ·
          refine ⟨3706485337753462487850371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2470990225168974991900247 3706485337753462487850371)
          ·
            refine ⟨5559728006630193731775557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3706485337753462487850371 5559728006630193731775557)
            ·
              refine ⟨1042449001243161324707917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5559728006630193731775557 1042449001243161324707917)
              ·
                refine ⟨390918375466185496765469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1042449001243161324707917 390918375466185496765469)
                ·
                  refine ⟨146594390799819561287051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390918375466185496765469 146594390799819561287051)
                  ·
                    rfl

theorem cell21_642356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_642356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642356 prefixEnd_642356 := by exact prefixLift 642356
  have htrace : WordTrace (prefixWord ++ tailWord_642356) baseStart_642356 baseEnd_642356 := by
    simpa [prefixWord, tailWord_642356, baseEnd_642356] using wordTrace_append hprefix tailTrace_642356
  have hstable : (prefixWord ++ tailWord_642356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642356).length < 2 ^ (prefixWord ++ tailWord_642356).sum := by decide
  have hdescent : baseEnd_642356 < baseStart_642356 := by decide
  rcases family_descends (prefixWord ++ tailWord_642356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642412 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_642412 : Nat := 118140960795 + 642412 * 2 ^ 59
def prefixEnd_642412 : Nat := 4983230072969 + 3 ^ 40 * 642412 * 2
def baseEnd_642412 : Nat := 146607170762775908353603

theorem tailTrace_642412 : CollatzResearch.WordTrace tailWord_642412 prefixEnd_642412 146607170762775908353603 := by
  unfold tailWord_642412
  simp only [CollatzResearch.WordTrace]
  refine ⟨11715345274329257039916745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15620460365772342719888993 11715345274329257039916745)
  ·
    refine ⟨8786508955746942779937559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11715345274329257039916745 8786508955746942779937559)
    ·
      refine ⟨13179763433620414169906339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8786508955746942779937559 13179763433620414169906339)
      ·
        refine ⟨19769645150430621254859509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13179763433620414169906339 19769645150430621254859509)
        ·
          refine ⟨1853404232852870742643079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19769645150430621254859509 1853404232852870742643079)
          ·
            refine ⟨2780106349279306113964619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853404232852870742643079 2780106349279306113964619)
            ·
              refine ⟨4170159523918959170946929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780106349279306113964619 4170159523918959170946929)
              ·
                refine ⟨3127619642939219378210197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4170159523918959170946929 3127619642939219378210197)
                ·
                  refine ⟨146607170762775908353603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3127619642939219378210197 146607170762775908353603)
                  ·
                    rfl

theorem cell21_642412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_642412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642412 prefixEnd_642412 := by exact prefixLift 642412
  have htrace : WordTrace (prefixWord ++ tailWord_642412) baseStart_642412 baseEnd_642412 := by
    simpa [prefixWord, tailWord_642412, baseEnd_642412] using wordTrace_append hprefix tailTrace_642412
  have hstable : (prefixWord ++ tailWord_642412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642412).length < 2 ^ (prefixWord ++ tailWord_642412).sum := by decide
  have hdescent : baseEnd_642412 < baseStart_642412 := by decide
  rcases family_descends (prefixWord ++ tailWord_642412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642446 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_642446 : Nat := 118140960795 + 642446 * 2 ^ 59
def prefixEnd_642446 : Nat := 4983230072969 + 3 ^ 40 * 642446 * 2
def baseEnd_642446 : Nat := 146614930025999404786867

theorem tailTrace_642446 : CollatzResearch.WordTrace tailWord_642446 prefixEnd_642446 146614930025999404786867 := by
  unfold tailWord_642446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928991328816917235821399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15621287087023558591047461 2928991328816917235821399)
  ·
    refine ⟨4393486993225375853732099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2928991328816917235821399 4393486993225375853732099)
    ·
      refine ⟨6590230489838063780598149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4393486993225375853732099 6590230489838063780598149)
      ·
        refine ⟨1235668216844636958862153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6590230489838063780598149 1235668216844636958862153)
        ·
          refine ⟨926751162633477719146615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1235668216844636958862153 926751162633477719146615)
          ·
            refine ⟨1390126743950216578719923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926751162633477719146615 1390126743950216578719923)
            ·
              refine ⟨2085190115925324868079885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390126743950216578719923 2085190115925324868079885)
              ·
                refine ⟨781946293471996825529957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2085190115925324868079885 781946293471996825529957)
                ·
                  refine ⟨146614930025999404786867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 781946293471996825529957 146614930025999404786867)
                  ·
                    rfl

theorem cell21_642446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_642446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642446 prefixEnd_642446 := by exact prefixLift 642446
  have htrace : WordTrace (prefixWord ++ tailWord_642446) baseStart_642446 baseEnd_642446 := by
    simpa [prefixWord, tailWord_642446, baseEnd_642446] using wordTrace_append hprefix tailTrace_642446
  have hstable : (prefixWord ++ tailWord_642446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642446).length < 2 ^ (prefixWord ++ tailWord_642446).sum := by decide
  have hdescent : baseEnd_642446 < baseStart_642446 := by decide
  rcases family_descends (prefixWord ++ tailWord_642446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642488 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 4]
def baseStart_642488 : Nat := 118140960795 + 642488 * 2 ^ 59
def prefixEnd_642488 : Nat := 4983230072969 + 3 ^ 40 * 642488 * 2
def baseEnd_642488 : Nat := 146624514998216665086781

theorem tailTrace_642488 : CollatzResearch.WordTrace tailWord_642488 prefixEnd_642488 146624514998216665086781 := by
  unfold tailWord_642488
  simp only [CollatzResearch.WordTrace]
  refine ⟨11716731248191589529800059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15622308330922119373066745 11716731248191589529800059)
  ·
    refine ⟨17575096872287384294700089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11716731248191589529800059 17575096872287384294700089)
    ·
      refine ⟨13181322654215538221025067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17575096872287384294700089 13181322654215538221025067)
      ·
        refine ⟨19771983981323307331537601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13181322654215538221025067 19771983981323307331537601)
        ·
          refine ⟨14828987985992480498653201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19771983981323307331537601 14828987985992480498653201)
          ·
            refine ⟨11121740989494360373989901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14828987985992480498653201 11121740989494360373989901)
            ·
              refine ⟨4170652871060385140246213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11121740989494360373989901 4170652871060385140246213)
              ·
                refine ⟨781997413323822213796165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4170652871060385140246213 781997413323822213796165)
                ·
                  refine ⟨146624514998216665086781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 781997413323822213796165 146624514998216665086781)
                  ·
                    rfl

theorem cell21_642488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_642488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642488 prefixEnd_642488 := by exact prefixLift 642488
  have htrace : WordTrace (prefixWord ++ tailWord_642488) baseStart_642488 baseEnd_642488 := by
    simpa [prefixWord, tailWord_642488, baseEnd_642488] using wordTrace_append hprefix tailTrace_642488
  have hstable : (prefixWord ++ tailWord_642488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642488).length < 2 ^ (prefixWord ++ tailWord_642488).sum := by decide
  have hdescent : baseEnd_642488 < baseStart_642488 := by decide
  rcases family_descends (prefixWord ++ tailWord_642488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642550 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_642550 : Nat := 118140960795 + 642550 * 2 ^ 59
def prefixEnd_642550 : Nat := 4983230072969 + 3 ^ 40 * 642550 * 2
def baseEnd_642550 : Nat := 146638664242918335053321

theorem tailTrace_642550 : CollatzResearch.WordTrace tailWord_642550 prefixEnd_642550 146638664242918335053321 := by
  unfold tailWord_642550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1464732738884910228022319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15623815881439042432238069 1464732738884910228022319)
  ·
    refine ⟨2197099108327365342033479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1464732738884910228022319 2197099108327365342033479)
    ·
      refine ⟨3295648662491048013050219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2197099108327365342033479 3295648662491048013050219)
      ·
        refine ⟨4943472993736572019575329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295648662491048013050219 4943472993736572019575329)
        ·
          refine ⟨3707604745302429014681497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4943472993736572019575329 3707604745302429014681497)
          ·
            refine ⟨2780703558976821761011123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3707604745302429014681497 2780703558976821761011123)
            ·
              refine ⟨4171055338465232641516685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780703558976821761011123 4171055338465232641516685)
              ·
                refine ⟨1564145751924462240568757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4171055338465232641516685 1564145751924462240568757)
                ·
                  refine ⟨146638664242918335053321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1564145751924462240568757 146638664242918335053321)
                  ·
                    rfl

theorem cell21_642550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_642550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642550 prefixEnd_642550 := by exact prefixLift 642550
  have htrace : WordTrace (prefixWord ++ tailWord_642550) baseStart_642550 baseEnd_642550 := by
    simpa [prefixWord, tailWord_642550, baseEnd_642550] using wordTrace_append hprefix tailTrace_642550
  have hstable : (prefixWord ++ tailWord_642550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642550).length < 2 ^ (prefixWord ++ tailWord_642550).sum := by decide
  have hdescent : baseEnd_642550 < baseStart_642550 := by decide
  rcases family_descends (prefixWord ++ tailWord_642550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642584 : List Nat := [2, 1, 2, 3, 4, 2, 1, 3, 3]
def baseStart_642584 : Nat := 118140960795 + 642584 * 2 ^ 59
def prefixEnd_642584 : Nat := 4983230072969 + 3 ^ 40 * 642584 * 2
def baseEnd_642584 : Nat := 146646423506141831486585

theorem tailTrace_642584 : CollatzResearch.WordTrace tailWord_642584 prefixEnd_642584 146646423506141831486585 := by
  unfold tailWord_642584
  simp only [CollatzResearch.WordTrace]
  refine ⟨11718481952017693727547403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15624642602690258303396537 11718481952017693727547403)
  ·
    refine ⟨17577722928026540591321105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11718481952017693727547403 17577722928026540591321105)
    ·
      refine ⟨13183292196019905443490829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17577722928026540591321105 13183292196019905443490829)
      ·
        refine ⟨4943734573507464541309061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13183292196019905443490829 4943734573507464541309061)
        ·
          refine ⟨926950232532649601495449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4943734573507464541309061 926950232532649601495449)
          ·
            refine ⟨695212674399487201121587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926950232532649601495449 695212674399487201121587)
            ·
              refine ⟨1042819011599230801682381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695212674399487201121587 1042819011599230801682381)
              ·
                refine ⟨391057129349711550630893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1042819011599230801682381 391057129349711550630893)
                ·
                  refine ⟨146646423506141831486585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391057129349711550630893 146646423506141831486585)
                  ·
                    rfl

theorem cell21_642584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 3].length) (baseStart_642584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642584 prefixEnd_642584 := by exact prefixLift 642584
  have htrace : WordTrace (prefixWord ++ tailWord_642584) baseStart_642584 baseEnd_642584 := by
    simpa [prefixWord, tailWord_642584, baseEnd_642584] using wordTrace_append hprefix tailTrace_642584
  have hstable : (prefixWord ++ tailWord_642584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642584).length < 2 ^ (prefixWord ++ tailWord_642584).sum := by decide
  have hdescent : baseEnd_642584 < baseStart_642584 := by decide
  rcases family_descends (prefixWord ++ tailWord_642584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642595 : List Nat := [1, 1, 1, 4, 5, 2, 7]
def baseStart_642595 : Nat := 118140960795 + 642595 * 2 ^ 59
def prefixEnd_642595 : Nat := 4983230072969 + 3 ^ 40 * 642595 * 2
def baseEnd_642595 : Nat := 16294325984000917422581

theorem tailTrace_642595 : CollatzResearch.WordTrace tailWord_642595 prefixEnd_642595 16294325984000917422581 := by
  unfold tailWord_642595
  simp only [CollatzResearch.WordTrace]
  refine ⟨23437365106995536333745239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15624910071330357555830159 23437365106995536333745239)
  ·
    refine ⟨35156047660493304500617859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23437365106995536333745239 35156047660493304500617859)
    ·
      refine ⟨52734071490739956750926789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35156047660493304500617859 52734071490739956750926789)
      ·
        refine ⟨9887638404513741890798773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52734071490739956750926789 9887638404513741890798773)
        ·
          refine ⟨926966100423163302262385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9887638404513741890798773 926966100423163302262385)
          ·
            refine ⟨695224575317372476696789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926966100423163302262385 695224575317372476696789)
            ·
              refine ⟨16294325984000917422581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 695224575317372476696789 16294325984000917422581)
              ·
                rfl

theorem cell21_642595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 7].length) (baseStart_642595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642595 prefixEnd_642595 := by exact prefixLift 642595
  have htrace : WordTrace (prefixWord ++ tailWord_642595) baseStart_642595 baseEnd_642595 := by
    simpa [prefixWord, tailWord_642595, baseEnd_642595] using wordTrace_append hprefix tailTrace_642595
  have hstable : (prefixWord ++ tailWord_642595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642595).length < 2 ^ (prefixWord ++ tailWord_642595).sum := by decide
  have hdescent : baseEnd_642595 < baseStart_642595 := by decide
  rcases family_descends (prefixWord ++ tailWord_642595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642660 : List Nat := [2, 3, 1, 1, 2, 5, 2, 2, 3]
def baseStart_642660 : Nat := 118140960795 + 642660 * 2 ^ 59
def prefixEnd_642660 : Nat := 4983230072969 + 3 ^ 40 * 642660 * 2
def baseEnd_642660 : Nat := 146663767741582588219763

theorem tailTrace_642660 : CollatzResearch.WordTrace tailWord_642660 prefixEnd_642660 146663767741582588219763 := by
  unfold tailWord_642660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11719867925880026217430717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15626490567840034956574289 11719867925880026217430717)
  ·
    refine ⟨4394950472205009831536519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11719867925880026217430717 4394950472205009831536519)
    ·
      refine ⟨6592425708307514747304779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4394950472205009831536519 6592425708307514747304779)
      ·
        refine ⟨9888638562461272120957169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6592425708307514747304779 9888638562461272120957169)
        ·
          refine ⟨7416478921845954090717877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9888638562461272120957169 7416478921845954090717877)
          ·
            refine ⟨695294898923058196004801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7416478921845954090717877 695294898923058196004801)
            ·
              refine ⟨521471174192293647003601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695294898923058196004801 521471174192293647003601)
              ·
                refine ⟨391103380644220235252701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521471174192293647003601 391103380644220235252701)
                ·
                  refine ⟨146663767741582588219763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391103380644220235252701 146663767741582588219763)
                  ·
                    rfl

theorem cell21_642660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_642660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642660 prefixEnd_642660 := by exact prefixLift 642660
  have htrace : WordTrace (prefixWord ++ tailWord_642660) baseStart_642660 baseEnd_642660 := by
    simpa [prefixWord, tailWord_642660, baseEnd_642660] using wordTrace_append hprefix tailTrace_642660
  have hstable : (prefixWord ++ tailWord_642660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642660).length < 2 ^ (prefixWord ++ tailWord_642660).sum := by decide
  have hdescent : baseEnd_642660 < baseStart_642660 := by decide
  rcases family_descends (prefixWord ++ tailWord_642660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642685 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 7]
def baseStart_642685 : Nat := 118140960795 + 642685 * 2 ^ 59
def prefixEnd_642685 : Nat := 4983230072969 + 3 ^ 40 * 642685 * 2
def baseEnd_642685 : Nat := 146669473082188100303045

theorem tailTrace_642685 : CollatzResearch.WordTrace tailWord_642685 prefixEnd_642685 146669473082188100303045 := by
  unfold tailWord_642685
  simp only [CollatzResearch.WordTrace]
  refine ⟨23440647676669481704521509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15627098451112987803014339 23440647676669481704521509)
  ·
    refine ⟨4395121439375527819597783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23440647676669481704521509 4395121439375527819597783)
    ·
      refine ⟨6592682159063291729396675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4395121439375527819597783 6592682159063291729396675)
      ·
        refine ⟨9889023238594937594095013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6592682159063291729396675 9889023238594937594095013)
        ·
          refine ⟨1854191857236550798892815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9889023238594937594095013 1854191857236550798892815)
          ·
            refine ⟨2781287785854826198339223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854191857236550798892815 2781287785854826198339223)
            ·
              refine ⟨4171931678782239297508835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781287785854826198339223 4171931678782239297508835)
              ·
                refine ⟨6257897518173358946263253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4171931678782239297508835 6257897518173358946263253)
                ·
                  refine ⟨146669473082188100303045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6257897518173358946263253 146669473082188100303045)
                  ·
                    rfl

theorem cell21_642685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_642685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642685 prefixEnd_642685 := by exact prefixLift 642685
  have htrace : WordTrace (prefixWord ++ tailWord_642685) baseStart_642685 baseEnd_642685 := by
    simpa [prefixWord, tailWord_642685, baseEnd_642685] using wordTrace_append hprefix tailTrace_642685
  have hstable : (prefixWord ++ tailWord_642685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642685).length < 2 ^ (prefixWord ++ tailWord_642685).sum := by decide
  have hdescent : baseEnd_642685 < baseStart_642685 := by decide
  rcases family_descends (prefixWord ++ tailWord_642685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642699 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 6]
def baseStart_642699 : Nat := 118140960795 + 642699 * 2 ^ 59
def prefixEnd_642699 : Nat := 4983230072969 + 3 ^ 40 * 642699 * 2
def baseEnd_642699 : Nat := 146672668072927187069683

theorem tailTrace_642699 : CollatzResearch.WordTrace tailWord_642699 prefixEnd_642699 146672668072927187069683 := by
  unfold tailWord_642699
  simp only [CollatzResearch.WordTrace]
  refine ⟨23441158298618762095531151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15627438865745841397020767 23441158298618762095531151)
  ·
    refine ⟨35161737447928143143296727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23441158298618762095531151 35161737447928143143296727)
    ·
      refine ⟨52742606171892214714945091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35161737447928143143296727 52742606171892214714945091)
      ·
        refine ⟨79113909257838322072417637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52742606171892214714945091 79113909257838322072417637)
        ·
          refine ⟨14833857985844685388578307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79113909257838322072417637 14833857985844685388578307)
          ·
            refine ⟨22250786978767028082867461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14833857985844685388578307 22250786978767028082867461)
            ·
              refine ⟨4172022558518817765537649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22250786978767028082867461 4172022558518817765537649)
              ·
                refine ⟨3129016918889113324153237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4172022558518817765537649 3129016918889113324153237)
                ·
                  refine ⟨146672668072927187069683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3129016918889113324153237 146672668072927187069683)
                  ·
                    rfl

theorem cell21_642699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_642699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642699 prefixEnd_642699 := by exact prefixLift 642699
  have htrace : WordTrace (prefixWord ++ tailWord_642699) baseStart_642699 baseEnd_642699 := by
    simpa [prefixWord, tailWord_642699, baseEnd_642699] using wordTrace_append hprefix tailTrace_642699
  have hstable : (prefixWord ++ tailWord_642699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642699).length < 2 ^ (prefixWord ++ tailWord_642699).sum := by decide
  have hdescent : baseEnd_642699 < baseStart_642699 := by decide
  rcases family_descends (prefixWord ++ tailWord_642699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642719 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 5]
def baseStart_642719 : Nat := 118140960795 + 642719 * 2 ^ 59
def prefixEnd_642719 : Nat := 4983230072969 + 3 ^ 40 * 642719 * 2
def baseEnd_642719 : Nat := 146677232345411596736309

theorem tailTrace_642719 : CollatzResearch.WordTrace tailWord_642719 prefixEnd_642719 146677232345411596736309 := by
  unfold tailWord_642719
  simp only [CollatzResearch.WordTrace]
  refine ⟨23441887758546305511259211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15627925172364203674172807 23441887758546305511259211)
  ·
    refine ⟨35162831637819458266888817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23441887758546305511259211 35162831637819458266888817)
    ·
      refine ⟨26372123728364593700166613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35162831637819458266888817 26372123728364593700166613)
      ·
        refine ⟨618096649883545164847655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 26372123728364593700166613 618096649883545164847655)
        ·
          refine ⟨927144974825317747271483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618096649883545164847655 927144974825317747271483)
          ·
            refine ⟨1390717462237976620907225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927144974825317747271483 1390717462237976620907225)
            ·
              refine ⟨1043038096678482465680419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1390717462237976620907225 1043038096678482465680419)
              ·
                refine ⟨1564557145017723698520629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043038096678482465680419 1564557145017723698520629)
                ·
                  refine ⟨146677232345411596736309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1564557145017723698520629 146677232345411596736309)
                  ·
                    rfl

theorem cell21_642719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 5].length) (baseStart_642719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642719 prefixEnd_642719 := by exact prefixLift 642719
  have htrace : WordTrace (prefixWord ++ tailWord_642719) baseStart_642719 baseEnd_642719 := by
    simpa [prefixWord, tailWord_642719, baseEnd_642719] using wordTrace_append hprefix tailTrace_642719
  have hstable : (prefixWord ++ tailWord_642719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642719).length < 2 ^ (prefixWord ++ tailWord_642719).sum := by decide
  have hdescent : baseEnd_642719 < baseStart_642719 := by decide
  rcases family_descends (prefixWord ++ tailWord_642719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642764 : List Nat := [2, 2, 1, 5, 3, 1, 7]
def baseStart_642764 : Nat := 118140960795 + 642764 * 2 ^ 59
def prefixEnd_642764 : Nat := 4983230072969 + 3 ^ 40 * 642764 * 2
def baseEnd_642764 : Nat := 16298611328722390942913

theorem tailTrace_642764 : CollatzResearch.WordTrace tailWord_642764 prefixEnd_642764 16298611328722390942913 := by
  unfold tailWord_642764
  simp only [CollatzResearch.WordTrace]
  refine ⟨11721764521691639098323673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15629019362255518797764897 11721764521691639098323673)
  ·
    refine ⟨8791323391268729323742755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11721764521691639098323673 8791323391268729323742755)
    ·
      refine ⟨13186985086903093985614133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8791323391268729323742755 13186985086903093985614133)
      ·
        refine ⟨1236279851897165061151325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13186985086903093985614133 1236279851897165061151325)
        ·
          refine ⟨463604944461436897931747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1236279851897165061151325 463604944461436897931747)
          ·
            refine ⟨695407416692155346897621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463604944461436897931747 695407416692155346897621)
            ·
              refine ⟨16298611328722390942913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 695407416692155346897621 16298611328722390942913)
              ·
                rfl

theorem cell21_642764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 7].length) (baseStart_642764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642764 prefixEnd_642764 := by exact prefixLift 642764
  have htrace : WordTrace (prefixWord ++ tailWord_642764) baseStart_642764 baseEnd_642764 := by
    simpa [prefixWord, tailWord_642764, baseEnd_642764] using wordTrace_append hprefix tailTrace_642764
  have hstable : (prefixWord ++ tailWord_642764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642764).length < 2 ^ (prefixWord ++ tailWord_642764).sum := by decide
  have hdescent : baseEnd_642764 < baseStart_642764 := by decide
  rcases family_descends (prefixWord ++ tailWord_642764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642775 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 6]
def baseStart_642775 : Nat := 118140960795 + 642775 * 2 ^ 59
def prefixEnd_642775 : Nat := 4983230072969 + 3 ^ 40 * 642775 * 2
def baseEnd_642775 : Nat := 146690012308367943802861

theorem tailTrace_642775 : CollatzResearch.WordTrace tailWord_642775 prefixEnd_642775 146690012308367943802861 := by
  unfold tailWord_642775
  simp only [CollatzResearch.WordTrace]
  refine ⟨23443930246343427075297779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15629286830895618050198519 23443930246343427075297779)
  ·
    refine ⟨35165895369515140612946669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23443930246343427075297779 35165895369515140612946669)
    ·
      refine ⟨13187210763568177729855001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35165895369515140612946669 13187210763568177729855001)
      ·
        refine ⟨9890408072676133297391251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13187210763568177729855001 9890408072676133297391251)
        ·
          refine ⟨14835612109014199946086877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9890408072676133297391251 14835612109014199946086877)
          ·
            refine ⟨5563354540880324979782579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14835612109014199946086877 5563354540880324979782579)
            ·
              refine ⟨8345031811320487469673869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5563354540880324979782579 8345031811320487469673869)
              ·
                refine ⟨3129386929245182801127701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8345031811320487469673869 3129386929245182801127701)
                ·
                  refine ⟨146690012308367943802861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3129386929245182801127701 146690012308367943802861)
                  ·
                    rfl

theorem cell21_642775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_642775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642775 prefixEnd_642775 := by exact prefixLift 642775
  have htrace : WordTrace (prefixWord ++ tailWord_642775) baseStart_642775 baseEnd_642775 := by
    simpa [prefixWord, tailWord_642775, baseEnd_642775] using wordTrace_append hprefix tailTrace_642775
  have hstable : (prefixWord ++ tailWord_642775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642775).length < 2 ^ (prefixWord ++ tailWord_642775).sum := by decide
  have hdescent : baseEnd_642775 < baseStart_642775 := by decide
  rcases family_descends (prefixWord ++ tailWord_642775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642778 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_642778 : Nat := 118140960795 + 642778 * 2 ^ 59
def prefixEnd_642778 : Nat := 4983230072969 + 3 ^ 40 * 642778 * 2
def baseEnd_642778 : Nat := 146690696949240605252855

theorem tailTrace_642778 : CollatzResearch.WordTrace tailWord_642778 prefixEnd_642778 146690696949240605252855 := by
  unfold tailWord_642778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5861009916333139646914247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15629359776888372391771325 5861009916333139646914247)
  ·
    refine ⟨8791514874499709470371371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5861009916333139646914247 8791514874499709470371371)
    ·
      refine ⟨13187272311749564205557057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8791514874499709470371371 13187272311749564205557057)
      ·
        refine ⟨9890454233812173154167793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13187272311749564205557057 9890454233812173154167793)
        ·
          refine ⟨7417840675359129865625845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9890454233812173154167793 7417840675359129865625845)
          ·
            refine ⟨695422563314918424902423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7417840675359129865625845 695422563314918424902423)
            ·
              refine ⟨1043133844972377637353635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695422563314918424902423 1043133844972377637353635)
              ·
                refine ⟨1564700767458566456030453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043133844972377637353635 1564700767458566456030453)
                ·
                  refine ⟨146690696949240605252855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1564700767458566456030453 146690696949240605252855)
                  ·
                    rfl

theorem cell21_642778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_642778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642778 prefixEnd_642778 := by exact prefixLift 642778
  have htrace : WordTrace (prefixWord ++ tailWord_642778) baseStart_642778 baseEnd_642778 := by
    simpa [prefixWord, tailWord_642778, baseEnd_642778] using wordTrace_append hprefix tailTrace_642778
  have hstable : (prefixWord ++ tailWord_642778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642778).length < 2 ^ (prefixWord ++ tailWord_642778).sum := by decide
  have hdescent : baseEnd_642778 < baseStart_642778 := by decide
  rcases family_descends (prefixWord ++ tailWord_642778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642823 : List Nat := [1, 1, 4, 4, 3, 8]
def baseStart_642823 : Nat := 118140960795 + 642823 * 2 ^ 59
def prefixEnd_642823 : Nat := 4983230072969 + 3 ^ 40 * 642823 * 2
def baseEnd_642823 : Nat := 5433369131938167666769

theorem tailTrace_642823 : CollatzResearch.WordTrace tailWord_642823 prefixEnd_642823 5433369131938167666769 := by
  unfold tailWord_642823
  simp only [CollatzResearch.WordTrace]
  refine ⟨23445680950169531273045123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15630453966779687515363415 23445680950169531273045123)
  ·
    refine ⟨35168521425254296909567685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23445680950169531273045123 35168521425254296909567685)
    ·
      refine ⟨6594097767235180670543941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35168521425254296909567685 6594097767235180670543941)
      ·
        refine ⟨1236393331356596375726989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6594097767235180670543941 1236393331356596375726989)
        ·
          refine ⟨463647499258723640897621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1236393331356596375726989 463647499258723640897621)
          ·
            refine ⟨5433369131938167666769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 463647499258723640897621 5433369131938167666769)
            ·
              rfl

theorem cell21_642823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 8].length) (baseStart_642823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642823 prefixEnd_642823 := by exact prefixLift 642823
  have htrace : WordTrace (prefixWord ++ tailWord_642823) baseStart_642823 baseEnd_642823 := by
    simpa [prefixWord, tailWord_642823, baseEnd_642823] using wordTrace_append hprefix tailTrace_642823
  have hstable : (prefixWord ++ tailWord_642823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642823).length < 2 ^ (prefixWord ++ tailWord_642823).sum := by decide
  have hdescent : baseEnd_642823 < baseStart_642823 := by decide
  rcases family_descends (prefixWord ++ tailWord_642823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642916 : List Nat := [2, 3, 1, 1, 5, 2, 2, 5]
def baseStart_642916 : Nat := 118140960795 + 642916 * 2 ^ 59
def prefixEnd_642916 : Nat := 4983230072969 + 3 ^ 40 * 642916 * 2
def baseEnd_642916 : Nat := 48907396809794343984191

theorem tailTrace_642916 : CollatzResearch.WordTrace tailWord_642916 prefixEnd_642916 48907396809794343984191 := by
  unfold tailWord_642916
  simp only [CollatzResearch.WordTrace]
  refine ⟨11724536469416304078090301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15632715292555072104120401 11724536469416304078090301)
  ·
    refine ⟨4396701176031114029283863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11724536469416304078090301 4396701176031114029283863)
    ·
      refine ⟨6595051764046671043925795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4396701176031114029283863 6595051764046671043925795)
      ·
        refine ⟨9892577646070006565888693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6595051764046671043925795 9892577646070006565888693)
        ·
          refine ⟨927429154319063115552065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9892577646070006565888693 927429154319063115552065)
          ·
            refine ⟨695571865739297336664049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 927429154319063115552065 695571865739297336664049)
            ·
              refine ⟨521678899304473002498037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695571865739297336664049 521678899304473002498037)
              ·
                refine ⟨48907396809794343984191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 521678899304473002498037 48907396809794343984191)
                ·
                  rfl

theorem cell21_642916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_642916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642916 prefixEnd_642916 := by exact prefixLift 642916
  have htrace : WordTrace (prefixWord ++ tailWord_642916) baseStart_642916 baseEnd_642916 := by
    simpa [prefixWord, tailWord_642916, baseEnd_642916] using wordTrace_append hprefix tailTrace_642916
  have hstable : (prefixWord ++ tailWord_642916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642916).length < 2 ^ (prefixWord ++ tailWord_642916).sum := by decide
  have hdescent : baseEnd_642916 < baseStart_642916 := by decide
  rcases family_descends (prefixWord ++ tailWord_642916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642947 : List Nat := [1, 1, 1, 3, 4, 3, 3, 2, 3]
def baseStart_642947 : Nat := 118140960795 + 642947 * 2 ^ 59
def prefixEnd_642947 : Nat := 4983230072969 + 3 ^ 40 * 642947 * 2
def baseEnd_642947 : Nat := 146729265051733866935843

theorem tailTrace_642947 : CollatzResearch.WordTrace tailWord_642947 prefixEnd_642947 146729265051733866935843 := by
  unfold tailWord_642947
  simp only [CollatzResearch.WordTrace]
  refine ⟨23450203601720300450559095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15633469067813533633706063 23450203601720300450559095)
  ·
    refine ⟨35175305402580450675838643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23450203601720300450559095 35175305402580450675838643)
    ·
      refine ⟨52762958103870676013757965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35175305402580450675838643 52762958103870676013757965)
      ·
        refine ⟨19786109288951503505159237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52762958103870676013757965 19786109288951503505159237)
        ·
          refine ⟨3709895491678406907217357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19786109288951503505159237 3709895491678406907217357)
          ·
            refine ⟨1391210809379402590206509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3709895491678406907217357 1391210809379402590206509)
            ·
              refine ⟨521704053517275971327441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1391210809379402590206509 521704053517275971327441)
              ·
                refine ⟨391278040137956978495581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521704053517275971327441 391278040137956978495581)
                ·
                  refine ⟨146729265051733866935843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391278040137956978495581 146729265051733866935843)
                  ·
                    rfl

theorem cell21_642947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 3].length) (baseStart_642947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_642947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_642947 prefixEnd_642947 := by exact prefixLift 642947
  have htrace : WordTrace (prefixWord ++ tailWord_642947) baseStart_642947 baseEnd_642947 := by
    simpa [prefixWord, tailWord_642947, baseEnd_642947] using wordTrace_append hprefix tailTrace_642947
  have hstable : (prefixWord ++ tailWord_642947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642947).length < 2 ^ (prefixWord ++ tailWord_642947).sum := by decide
  have hdescent : baseEnd_642947 < baseStart_642947 := by decide
  rcases family_descends (prefixWord ++ tailWord_642947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643003 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 4]
def baseStart_643003 : Nat := 118140960795 + 643003 * 2 ^ 59
def prefixEnd_643003 : Nat := 4983230072969 + 3 ^ 40 * 643003 * 2
def baseEnd_643003 : Nat := 146742045014690214002395

theorem tailTrace_643003 : CollatzResearch.WordTrace tailWord_643003 prefixEnd_643003 146742045014690214002395 := by
  unfold tailWord_643003
  simp only [CollatzResearch.WordTrace]
  refine ⟨23452246089517422014597663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15634830726344948009731775 23452246089517422014597663)
  ·
    refine ⟨35178369134276133021896495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23452246089517422014597663 35178369134276133021896495)
    ·
      refine ⟨52767553701414199532844743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35178369134276133021896495 52767553701414199532844743)
      ·
        refine ⟨79151330552121299299267115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52767553701414199532844743 79151330552121299299267115)
        ·
          refine ⟨118726995828181948948900673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79151330552121299299267115 118726995828181948948900673)
          ·
            refine ⟨89045246871136461711675505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118726995828181948948900673 89045246871136461711675505)
            ·
              refine ⟨66783935153352346283756629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89045246871136461711675505 66783935153352346283756629)
              ·
                refine ⟨782624240078347808012773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 66783935153352346283756629 782624240078347808012773)
                ·
                  refine ⟨146742045014690214002395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 782624240078347808012773 146742045014690214002395)
                  ·
                    rfl

theorem cell21_643003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 4].length) (baseStart_643003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643003 prefixEnd_643003 := by exact prefixLift 643003
  have htrace : WordTrace (prefixWord ++ tailWord_643003) baseStart_643003 baseEnd_643003 := by
    simpa [prefixWord, tailWord_643003, baseEnd_643003] using wordTrace_append hprefix tailTrace_643003
  have hstable : (prefixWord ++ tailWord_643003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643003).length < 2 ^ (prefixWord ++ tailWord_643003).sum := by decide
  have hdescent : baseEnd_643003 < baseStart_643003 := by decide
  rcases family_descends (prefixWord ++ tailWord_643003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643020 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 4]
def baseStart_643020 : Nat := 118140960795 + 643020 * 2 ^ 59
def prefixEnd_643020 : Nat := 4983230072969 + 3 ^ 40 * 643020 * 2
def baseEnd_643020 : Nat := 146745924646301962219027

theorem tailTrace_643020 : CollatzResearch.WordTrace tailWord_643020 prefixEnd_643020 146745924646301962219027 := by
  unfold tailWord_643020
  simp only [CollatzResearch.WordTrace]
  refine ⟨11726433065227916958983257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15635244086970555945311009 11726433065227916958983257)
  ·
    refine ⟨8794824798920937719237443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11726433065227916958983257 8794824798920937719237443)
    ·
      refine ⟨13192237198381406578856165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8794824798920937719237443 13192237198381406578856165)
      ·
        refine ⟨2473544474696513733535531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13192237198381406578856165 2473544474696513733535531)
        ·
          refine ⟨3710316712044770600303297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2473544474696513733535531 3710316712044770600303297)
          ·
            refine ⟨2782737534033577950227473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3710316712044770600303297 2782737534033577950227473)
            ·
              refine ⟨2087053150525183462670605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2782737534033577950227473 2087053150525183462670605)
              ·
                refine ⟨782644931446943798501477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2087053150525183462670605 782644931446943798501477)
                ·
                  refine ⟨146745924646301962219027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 782644931446943798501477 146745924646301962219027)
                  ·
                    rfl

theorem cell21_643020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_643020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643020 prefixEnd_643020 := by exact prefixLift 643020
  have htrace : WordTrace (prefixWord ++ tailWord_643020) baseStart_643020 baseEnd_643020 := by
    simpa [prefixWord, tailWord_643020, baseEnd_643020] using wordTrace_append hprefix tailTrace_643020
  have hstable : (prefixWord ++ tailWord_643020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643020).length < 2 ^ (prefixWord ++ tailWord_643020).sum := by decide
  have hdescent : baseEnd_643020 < baseStart_643020 := by decide
  rcases family_descends (prefixWord ++ tailWord_643020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643048 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_643048 : Nat := 118140960795 + 643048 * 2 ^ 59
def prefixEnd_643048 : Nat := 4983230072969 + 3 ^ 40 * 643048 * 2
def baseEnd_643048 : Nat := 146752314627780135752303

theorem tailTrace_643048 : CollatzResearch.WordTrace tailWord_643048 prefixEnd_643048 146752314627780135752303 := by
  unfold tailWord_643048
  simp only [CollatzResearch.WordTrace]
  refine ⟨11726943687177197349992899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15635924916236263133323865 11726943687177197349992899)
  ·
    refine ⟨17590415530765796024989349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11726943687177197349992899 17590415530765796024989349)
    ·
      refine ⟨3298202912018586754685503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17590415530765796024989349 3298202912018586754685503)
      ·
        refine ⟨4947304368027880132028255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3298202912018586754685503 4947304368027880132028255)
        ·
          refine ⟨7420956552041820198042383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4947304368027880132028255 7420956552041820198042383)
          ·
            refine ⟨11131434828062730297063575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420956552041820198042383 11131434828062730297063575)
            ·
              refine ⟨16697152242094095445595363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11131434828062730297063575 16697152242094095445595363)
              ·
                refine ⟨25045728363141143168393045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16697152242094095445595363 25045728363141143168393045)
                ·
                  refine ⟨146752314627780135752303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25045728363141143168393045 146752314627780135752303)
                  ·
                    rfl

theorem cell21_643048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_643048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643048 prefixEnd_643048 := by exact prefixLift 643048
  have htrace : WordTrace (prefixWord ++ tailWord_643048) baseStart_643048 baseEnd_643048 := by
    simpa [prefixWord, tailWord_643048, baseEnd_643048] using wordTrace_append hprefix tailTrace_643048
  have hstable : (prefixWord ++ tailWord_643048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643048).length < 2 ^ (prefixWord ++ tailWord_643048).sum := by decide
  have hdescent : baseEnd_643048 < baseStart_643048 := by decide
  rcases family_descends (prefixWord ++ tailWord_643048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643065 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 5]
def baseStart_643065 : Nat := 118140960795 + 643065 * 2 ^ 59
def prefixEnd_643065 : Nat := 4983230072969 + 3 ^ 40 * 643065 * 2
def baseEnd_643065 : Nat := 146756194259391883968935

theorem tailTrace_643065 : CollatzResearch.WordTrace tailWord_643065 prefixEnd_643065 146756194259391883968935 := by
  unfold tailWord_643065
  simp only [CollatzResearch.WordTrace]
  refine ⟨23454507415292806603354649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15636338276861871068903099 23454507415292806603354649)
  ·
    refine ⟨17590880561469604952515987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23454507415292806603354649 17590880561469604952515987)
    ·
      refine ⟨26386320842204407428773981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17590880561469604952515987 26386320842204407428773981)
      ·
        refine ⟨9894870315826652785790243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26386320842204407428773981 9894870315826652785790243)
        ·
          refine ⟨14842305473739979178685365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9894870315826652785790243 14842305473739979178685365)
          ·
            refine ⟨1391466138163123048001753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14842305473739979178685365 1391466138163123048001753)
            ·
              refine ⟨1043599603622342286001315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391466138163123048001753 1043599603622342286001315)
              ·
                refine ⟨1565399405433513429001973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043599603622342286001315 1565399405433513429001973)
                ·
                  refine ⟨146756194259391883968935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1565399405433513429001973 146756194259391883968935)
                  ·
                    rfl

theorem cell21_643065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_643065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643065 prefixEnd_643065 := by exact prefixLift 643065
  have htrace : WordTrace (prefixWord ++ tailWord_643065) baseStart_643065 baseEnd_643065 := by
    simpa [prefixWord, tailWord_643065, baseEnd_643065] using wordTrace_append hprefix tailTrace_643065
  have hstable : (prefixWord ++ tailWord_643065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643065).length < 2 ^ (prefixWord ++ tailWord_643065).sum := by decide
  have hdescent : baseEnd_643065 < baseStart_643065 := by decide
  rcases family_descends (prefixWord ++ tailWord_643065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643085 : List Nat := [1, 7, 1, 2, 1, 1, 1, 7]
def baseStart_643085 : Nat := 118140960795 + 643085 * 2 ^ 59
def prefixEnd_643085 : Nat := 4983230072969 + 3 ^ 40 * 643085 * 2
def baseEnd_643085 : Nat := 48920252843958764545187

theorem tailTrace_643085 : CollatzResearch.WordTrace tailWord_643085 prefixEnd_643085 48920252843958764545187 := by
  unfold tailWord_643085
  simp only [CollatzResearch.WordTrace]
  refine ⟨23455236875220350019082709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15636824583480233346055139 23455236875220350019082709)
  ·
    refine ⟨549732114262976953572251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23455236875220350019082709 549732114262976953572251)
    ·
      refine ⟨824598171394465430358377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549732114262976953572251 824598171394465430358377)
      ·
        refine ⟨618448628545849072768783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 824598171394465430358377 618448628545849072768783)
        ·
          refine ⟨927672942818773609153175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618448628545849072768783 927672942818773609153175)
          ·
            refine ⟨1391509414228160413729763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927672942818773609153175 1391509414228160413729763)
            ·
              refine ⟨2087264121342240620594645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391509414228160413729763 2087264121342240620594645)
              ·
                refine ⟨48920252843958764545187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2087264121342240620594645 48920252843958764545187)
                ·
                  rfl

theorem cell21_643085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 7].length) (baseStart_643085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643085 prefixEnd_643085 := by exact prefixLift 643085
  have htrace : WordTrace (prefixWord ++ tailWord_643085) baseStart_643085 baseEnd_643085 := by
    simpa [prefixWord, tailWord_643085, baseEnd_643085] using wordTrace_append hprefix tailTrace_643085
  have hstable : (prefixWord ++ tailWord_643085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643085).length < 2 ^ (prefixWord ++ tailWord_643085).sum := by decide
  have hdescent : baseEnd_643085 < baseStart_643085 := by decide
  rcases family_descends (prefixWord ++ tailWord_643085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643186 : List Nat := [3, 2, 1, 2, 2, 2, 3, 6]
def baseStart_643186 : Nat := 118140960795 + 643186 * 2 ^ 59
def prefixEnd_643186 : Nat := 4983230072969 + 3 ^ 40 * 643186 * 2
def baseEnd_643186 : Nat := 48927936035974187484007

theorem tailTrace_643186 : CollatzResearch.WordTrace tailWord_643186 prefixEnd_643186 48927936035974187484007 := by
  unfold tailWord_643186
  simp only [CollatzResearch.WordTrace]
  refine ⟨5864730161963611067127353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15639280431902962845672941 5864730161963611067127353)
  ·
    refine ⟨4398547621472708300345515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5864730161963611067127353 4398547621472708300345515)
    ·
      refine ⟨6597821432209062450518273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4398547621472708300345515 6597821432209062450518273)
      ·
        refine ⟨4948366074156796837888705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6597821432209062450518273 4948366074156796837888705)
        ·
          refine ⟨3711274555617597628416529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4948366074156796837888705 3711274555617597628416529)
          ·
            refine ⟨2783455916713198221312397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3711274555617597628416529 2783455916713198221312397)
            ·
              refine ⟨1043795968767449332992149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2783455916713198221312397 1043795968767449332992149)
              ·
                refine ⟨48927936035974187484007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1043795968767449332992149 48927936035974187484007)
                ·
                  rfl

theorem cell21_643186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_643186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643186 prefixEnd_643186 := by exact prefixLift 643186
  have htrace : WordTrace (prefixWord ++ tailWord_643186) baseStart_643186 baseEnd_643186 := by
    simpa [prefixWord, tailWord_643186, baseEnd_643186] using wordTrace_append hprefix tailTrace_643186
  have hstable : (prefixWord ++ tailWord_643186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643186).length < 2 ^ (prefixWord ++ tailWord_643186).sum := by decide
  have hdescent : baseEnd_643186 < baseStart_643186 := by decide
  rcases family_descends (prefixWord ++ tailWord_643186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643234 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_643234 : Nat := 118140960795 + 643234 * 2 ^ 59
def prefixEnd_643234 : Nat := 4983230072969 + 3 ^ 40 * 643234 * 2
def baseEnd_643234 : Nat := 146794762361885145651923

theorem tailTrace_643234 : CollatzResearch.WordTrace tailWord_643234 prefixEnd_643234 146794762361885145651923 := by
  unfold tailWord_643234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5865167837920137116564189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15640447567787032310837837 5865167837920137116564189)
  ·
    refine ⟨2199437939220051418711571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5865167837920137116564189 2199437939220051418711571)
    ·
      refine ⟨3299156908830077128067357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199437939220051418711571 3299156908830077128067357)
      ·
        refine ⟨1237183840811278923025259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3299156908830077128067357 1237183840811278923025259)
        ·
          refine ⟨1855775761216918384537889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237183840811278923025259 1855775761216918384537889)
          ·
            refine ⟨1391831820912688788403417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1855775761216918384537889 1391831820912688788403417)
            ·
              refine ⟨1043873865684516591302563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391831820912688788403417 1043873865684516591302563)
              ·
                refine ⟨1565810798526774886953845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043873865684516591302563 1565810798526774886953845)
                ·
                  refine ⟨146794762361885145651923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1565810798526774886953845 146794762361885145651923)
                  ·
                    rfl

theorem cell21_643234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_643234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643234 prefixEnd_643234 := by exact prefixLift 643234
  have htrace : WordTrace (prefixWord ++ tailWord_643234) baseStart_643234 baseEnd_643234 := by
    simpa [prefixWord, tailWord_643234, baseEnd_643234] using wordTrace_append hprefix tailTrace_643234
  have hstable : (prefixWord ++ tailWord_643234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643234).length < 2 ^ (prefixWord ++ tailWord_643234).sum := by decide
  have hdescent : baseEnd_643234 < baseStart_643234 := by decide
  rcases family_descends (prefixWord ++ tailWord_643234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643299 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 4]
def baseStart_643299 : Nat := 118140960795 + 643299 * 2 ^ 59
def prefixEnd_643299 : Nat := 4983230072969 + 3 ^ 40 * 643299 * 2
def baseEnd_643299 : Nat := 146809596247459477068457

theorem tailTrace_643299 : CollatzResearch.WordTrace tailWord_643299 prefixEnd_643299 146809596247459477068457 := by
  unfold tailWord_643299
  simp only [CollatzResearch.WordTrace]
  refine ⟨23463042096445064567372951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15642028064296709711581967 23463042096445064567372951)
  ·
    refine ⟨35194563144667596851059427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23463042096445064567372951 35194563144667596851059427)
    ·
      refine ⟨52791844717001395276589141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35194563144667596851059427 52791844717001395276589141)
      ·
        refine ⟨618654430277360100897529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 52791844717001395276589141 618654430277360100897529)
        ·
          refine ⟨463990822708020075673147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618654430277360100897529 463990822708020075673147)
          ·
            refine ⟨695986234062030113509721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463990822708020075673147 695986234062030113509721)
            ·
              refine ⟨521989675546522585132291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695986234062030113509721 521989675546522585132291)
              ·
                refine ⟨782984513319783877698437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521989675546522585132291 782984513319783877698437)
                ·
                  refine ⟨146809596247459477068457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 782984513319783877698437 146809596247459477068457)
                  ·
                    rfl

theorem cell21_643299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 4].length) (baseStart_643299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643299 prefixEnd_643299 := by exact prefixLift 643299
  have htrace : WordTrace (prefixWord ++ tailWord_643299) baseStart_643299 baseEnd_643299 := by
    simpa [prefixWord, tailWord_643299, baseEnd_643299] using wordTrace_append hprefix tailTrace_643299
  have hstable : (prefixWord ++ tailWord_643299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643299).length < 2 ^ (prefixWord ++ tailWord_643299).sum := by decide
  have hdescent : baseEnd_643299 < baseStart_643299 := by decide
  rcases family_descends (prefixWord ++ tailWord_643299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643307 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 4]
def baseStart_643307 : Nat := 118140960795 + 643307 * 2 ^ 59
def prefixEnd_643307 : Nat := 4983230072969 + 3 ^ 40 * 643307 * 2
def baseEnd_643307 : Nat := 146811421956453240935107

theorem tailTrace_643307 : CollatzResearch.WordTrace tailWord_643307 prefixEnd_643307 146811421956453240935107 := by
  unfold tailWord_643307
  simp only [CollatzResearch.WordTrace]
  refine ⟨23463333880416081933664175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15642222586944054622442783 23463333880416081933664175)
  ·
    refine ⟨35195000820624122900496263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23463333880416081933664175 35195000820624122900496263)
    ·
      refine ⟨52792501230936184350744395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35195000820624122900496263 52792501230936184350744395)
      ·
        refine ⟨79188751846404276526116593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52792501230936184350744395 79188751846404276526116593)
        ·
          refine ⟨59391563884803207394587445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79188751846404276526116593 59391563884803207394587445)
          ·
            refine ⟨5567959114200300693242573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59391563884803207394587445 5567959114200300693242573)
            ·
              refine ⟨2087984667825112759965965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5567959114200300693242573 2087984667825112759965965)
              ·
                refine ⟨782994250434417284987237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2087984667825112759965965 782994250434417284987237)
                ·
                  refine ⟨146811421956453240935107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 782994250434417284987237 146811421956453240935107)
                  ·
                    rfl

theorem cell21_643307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 4].length) (baseStart_643307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643307 prefixEnd_643307 := by exact prefixLift 643307
  have htrace : WordTrace (prefixWord ++ tailWord_643307) baseStart_643307 baseEnd_643307 := by
    simpa [prefixWord, tailWord_643307, baseEnd_643307] using wordTrace_append hprefix tailTrace_643307
  have hstable : (prefixWord ++ tailWord_643307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643307).length < 2 ^ (prefixWord ++ tailWord_643307).sum := by decide
  have hdescent : baseEnd_643307 < baseStart_643307 := by decide
  rcases family_descends (prefixWord ++ tailWord_643307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643352 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_643352 : Nat := 118140960795 + 643352 * 2 ^ 59
def prefixEnd_643352 : Nat := 4983230072969 + 3 ^ 40 * 643352 * 2
def baseEnd_643352 : Nat := 146821691569543162685015

theorem tailTrace_643352 : CollatzResearch.WordTrace tailWord_643352 prefixEnd_643352 146821691569543162685015 := by
  unfold tailWord_643352
  simp only [CollatzResearch.WordTrace]
  refine ⟨11732487582626527309526155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15643316776835369746034873 11732487582626527309526155)
  ·
    refine ⟨17598731373939790964289233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11732487582626527309526155 17598731373939790964289233)
    ·
      refine ⟨13199048530454843223216925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17598731373939790964289233 13199048530454843223216925)
      ·
        refine ⟨4949643198920566208706347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13199048530454843223216925 4949643198920566208706347)
        ·
          refine ⟨7424464798380849313059521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4949643198920566208706347 7424464798380849313059521)
          ·
            refine ⟨5568348598785636984794641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7424464798380849313059521 5568348598785636984794641)
            ·
              refine ⟨4176261449089227738595981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5568348598785636984794641 4176261449089227738595981)
              ·
                refine ⟨1566098043408460401973493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4176261449089227738595981 1566098043408460401973493)
                ·
                  refine ⟨146821691569543162685015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1566098043408460401973493 146821691569543162685015)
                  ·
                    rfl

theorem cell21_643352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_643352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643352 prefixEnd_643352 := by exact prefixLift 643352
  have htrace : WordTrace (prefixWord ++ tailWord_643352) baseStart_643352 baseEnd_643352 := by
    simpa [prefixWord, tailWord_643352, baseEnd_643352] using wordTrace_append hprefix tailTrace_643352
  have hstable : (prefixWord ++ tailWord_643352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643352).length < 2 ^ (prefixWord ++ tailWord_643352).sum := by decide
  have hdescent : baseEnd_643352 < baseStart_643352 := by decide
  rcases family_descends (prefixWord ++ tailWord_643352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643386 : List Nat := [3, 1, 1, 1, 4, 3, 2, 3, 3]
def baseStart_643386 : Nat := 118140960795 + 643386 * 2 ^ 59
def prefixEnd_643386 : Nat := 4983230072969 + 3 ^ 40 * 643386 * 2
def baseEnd_643386 : Nat := 146829450832766659118279

theorem tailTrace_643386 : CollatzResearch.WordTrace tailWord_643386 prefixEnd_643386 146829450832766659118279 := by
  unfold tailWord_643386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5866553811782469606447503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15644143498086585617193341 5866553811782469606447503)
  ·
    refine ⟨8799830717673704409671255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5866553811782469606447503 8799830717673704409671255)
    ·
      refine ⟨13199746076510556614506883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8799830717673704409671255 13199746076510556614506883)
      ·
        refine ⟨19799619114765834921760325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13199746076510556614506883 19799619114765834921760325)
        ·
          refine ⟨3712428584018594047830061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19799619114765834921760325 3712428584018594047830061)
          ·
            refine ⟨1392160719006972767936273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3712428584018594047830061 1392160719006972767936273)
            ·
              refine ⟨1044120539255229575952205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1392160719006972767936273 1044120539255229575952205)
              ·
                refine ⟨391545202220711090982077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1044120539255229575952205 391545202220711090982077)
                ·
                  refine ⟨146829450832766659118279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391545202220711090982077 146829450832766659118279)
                  ·
                    rfl

theorem cell21_643386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_643386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643386 prefixEnd_643386 := by exact prefixLift 643386
  have htrace : WordTrace (prefixWord ++ tailWord_643386) baseStart_643386 baseEnd_643386 := by
    simpa [prefixWord, tailWord_643386, baseEnd_643386] using wordTrace_append hprefix tailTrace_643386
  have hstable : (prefixWord ++ tailWord_643386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643386).length < 2 ^ (prefixWord ++ tailWord_643386).sum := by decide
  have hdescent : baseEnd_643386 < baseStart_643386 := by decide
  rcases family_descends (prefixWord ++ tailWord_643386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643428 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_643428 : Nat := 118140960795 + 643428 * 2 ^ 59
def prefixEnd_643428 : Nat := 4983230072969 + 3 ^ 40 * 643428 * 2
def baseEnd_643428 : Nat := 146839035804983919418193

theorem tailTrace_643428 : CollatzResearch.WordTrace tailWord_643428 prefixEnd_643428 146839035804983919418193 := by
  unfold tailWord_643428
  simp only [CollatzResearch.WordTrace]
  refine ⟨11733873556488859799409469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15645164741985146399212625 11733873556488859799409469)
  ·
    refine ⟨4400202583683322424778551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11733873556488859799409469 4400202583683322424778551)
    ·
      refine ⟨6600303875524983637167827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4400202583683322424778551 6600303875524983637167827)
      ·
        refine ⟨9900455813287475455751741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6600303875524983637167827 9900455813287475455751741)
        ·
          refine ⟨3712670929982803295906903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9900455813287475455751741 3712670929982803295906903)
          ·
            refine ⟨5569006394974204943860355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712670929982803295906903 5569006394974204943860355)
            ·
              refine ⟨8353509592461307415790533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5569006394974204943860355 8353509592461307415790533)
              ·
                refine ⟨1566283048586495140460725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8353509592461307415790533 1566283048586495140460725)
                ·
                  refine ⟨146839035804983919418193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1566283048586495140460725 146839035804983919418193)
                  ·
                    rfl

theorem cell21_643428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_643428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643428 prefixEnd_643428 := by exact prefixLift 643428
  have htrace : WordTrace (prefixWord ++ tailWord_643428) baseStart_643428 baseEnd_643428 := by
    simpa [prefixWord, tailWord_643428, baseEnd_643428] using wordTrace_append hprefix tailTrace_643428
  have hstable : (prefixWord ++ tailWord_643428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643428).length < 2 ^ (prefixWord ++ tailWord_643428).sum := by decide
  have hdescent : baseEnd_643428 < baseStart_643428 := by decide
  rcases family_descends (prefixWord ++ tailWord_643428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643431 : List Nat := [1, 1, 5, 1, 3, 3, 2, 5]
def baseStart_643431 : Nat := 118140960795 + 643431 * 2 ^ 59
def prefixEnd_643431 : Nat := 4983230072969 + 3 ^ 40 * 643431 * 2
def baseEnd_643431 : Nat := 48946573481952193622729

theorem tailTrace_643431 : CollatzResearch.WordTrace tailWord_643431 prefixEnd_643431 48946573481952193622729 := by
  unfold tailWord_643431
  simp only [CollatzResearch.WordTrace]
  refine ⟨23467856531966851111178147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15645237687977900740785431 23467856531966851111178147)
  ·
    refine ⟨35201784797950276666767221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23467856531966851111178147 35201784797950276666767221)
    ·
      refine ⟨3300167324807838437509427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35201784797950276666767221 3300167324807838437509427)
      ·
        refine ⟨4950250987211757656264141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3300167324807838437509427 4950250987211757656264141)
        ·
          refine ⟨1856344120204409121099053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4950250987211757656264141 1856344120204409121099053)
          ·
            refine ⟨696129045076653420412145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1856344120204409121099053 696129045076653420412145)
            ·
              refine ⟨522096783807490065309109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696129045076653420412145 522096783807490065309109)
              ·
                refine ⟨48946573481952193622729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 522096783807490065309109 48946573481952193622729)
                ·
                  rfl

theorem cell21_643431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 5].length) (baseStart_643431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643431 prefixEnd_643431 := by exact prefixLift 643431
  have htrace : WordTrace (prefixWord ++ tailWord_643431) baseStart_643431 baseEnd_643431 := by
    simpa [prefixWord, tailWord_643431, baseEnd_643431] using wordTrace_append hprefix tailTrace_643431
  have hstable : (prefixWord ++ tailWord_643431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643431).length < 2 ^ (prefixWord ++ tailWord_643431).sum := by decide
  have hdescent : baseEnd_643431 < baseStart_643431 := by decide
  rcases family_descends (prefixWord ++ tailWord_643431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643524 : List Nat := [2, 3, 3, 2, 3, 1, 1, 6]
def baseStart_643524 : Nat := 118140960795 + 643524 * 2 ^ 59
def prefixEnd_643524 : Nat := 4983230072969 + 3 ^ 40 * 643524 * 2
def baseEnd_643524 : Nat := 48953648104303028605999

theorem tailTrace_643524 : CollatzResearch.WordTrace tailWord_643524 prefixEnd_643524 48953648104303028605999 := by
  unfold tailWord_643524
  simp only [CollatzResearch.WordTrace]
  refine ⟨11735624260314963997156813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15647499013753285329542417 11735624260314963997156813)
  ·
    refine ⟨4400859097618111498933805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11735624260314963997156813 4400859097618111498933805)
    ·
      refine ⟨1650322161606791812100177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4400859097618111498933805 1650322161606791812100177)
      ·
        refine ⟨1237741621205093859075133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1650322161606791812100177 1237741621205093859075133)
        ·
          refine ⟨464153107951910197153175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1237741621205093859075133 464153107951910197153175)
          ·
            refine ⟨696229661927865295729763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464153107951910197153175 696229661927865295729763)
            ·
              refine ⟨1044344492891797943594645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696229661927865295729763 1044344492891797943594645)
              ·
                refine ⟨48953648104303028605999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1044344492891797943594645 48953648104303028605999)
                ·
                  rfl

theorem cell21_643524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 6].length) (baseStart_643524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643524 prefixEnd_643524 := by exact prefixLift 643524
  have htrace : WordTrace (prefixWord ++ tailWord_643524) baseStart_643524 baseEnd_643524 := by
    simpa [prefixWord, tailWord_643524, baseEnd_643524] using wordTrace_append hprefix tailTrace_643524
  have hstable : (prefixWord ++ tailWord_643524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643524).length < 2 ^ (prefixWord ++ tailWord_643524).sum := by decide
  have hdescent : baseEnd_643524 < baseStart_643524 := by decide
  rcases family_descends (prefixWord ++ tailWord_643524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643538 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_643538 : Nat := 118140960795 + 643538 * 2 ^ 59
def prefixEnd_643538 : Nat := 4983230072969 + 3 ^ 40 * 643538 * 2
def baseEnd_643538 : Nat := 146864139303648172584635

theorem tailTrace_643538 : CollatzResearch.WordTrace tailWord_643538 prefixEnd_643538 146864139303648172584635 := by
  unfold tailWord_643538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5867939785644802096330817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15647839428386138923548845 5867939785644802096330817)
  ·
    refine ⟨4400954839233601572248113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5867939785644802096330817 4400954839233601572248113)
    ·
      refine ⟨3300716129425201179186085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4400954839233601572248113 3300716129425201179186085)
      ·
        refine ⟨618884274267225221097391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3300716129425201179186085 618884274267225221097391)
        ·
          refine ⟨928326411400837831646087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618884274267225221097391 928326411400837831646087)
          ·
            refine ⟨1392489617101256747469131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928326411400837831646087 1392489617101256747469131)
            ·
              refine ⟨2088734425651885121203697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1392489617101256747469131 2088734425651885121203697)
              ·
                refine ⟨1566550819238913840902773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2088734425651885121203697 1566550819238913840902773)
                ·
                  refine ⟨146864139303648172584635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1566550819238913840902773 146864139303648172584635)
                  ·
                    rfl

theorem cell21_643538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_643538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643538 prefixEnd_643538 := by exact prefixLift 643538
  have htrace : WordTrace (prefixWord ++ tailWord_643538) baseStart_643538 baseEnd_643538 := by
    simpa [prefixWord, tailWord_643538, baseEnd_643538] using wordTrace_append hprefix tailTrace_643538
  have hstable : (prefixWord ++ tailWord_643538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643538).length < 2 ^ (prefixWord ++ tailWord_643538).sum := by decide
  have hdescent : baseEnd_643538 < baseStart_643538 := by decide
  rcases family_descends (prefixWord ++ tailWord_643538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643563 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 7]
def baseStart_643563 : Nat := 118140960795 + 643563 * 2 ^ 59
def prefixEnd_643563 : Nat := 4983230072969 + 3 ^ 40 * 643563 * 2
def baseEnd_643563 : Nat := 146869844644253684667917

theorem tailTrace_643563 : CollatzResearch.WordTrace tailWord_643563 prefixEnd_643563 146869844644253684667917 := by
  unfold tailWord_643563
  simp only [CollatzResearch.WordTrace]
  refine ⟨23472670967488637654983343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15648447311659091769988895 23472670967488637654983343)
  ·
    refine ⟨35209006451232956482475015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23472670967488637654983343 35209006451232956482475015)
    ·
      refine ⟨52813509676849434723712523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35209006451232956482475015 52813509676849434723712523)
      ·
        refine ⟨79220264515274152085568785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52813509676849434723712523 79220264515274152085568785)
        ·
          refine ⟨59415198386455614064176589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79220264515274152085568785 59415198386455614064176589)
          ·
            refine ⟨22280699394920855274066221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59415198386455614064176589 22280699394920855274066221)
            ·
              refine ⟨8355262273095320727774833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22280699394920855274066221 8355262273095320727774833)
              ·
                refine ⟨6266446704821490545831125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8355262273095320727774833 6266446704821490545831125)
                ·
                  refine ⟨146869844644253684667917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6266446704821490545831125 146869844644253684667917)
                  ·
                    rfl

theorem cell21_643563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_643563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643563 prefixEnd_643563 := by exact prefixLift 643563
  have htrace : WordTrace (prefixWord ++ tailWord_643563) baseStart_643563 baseEnd_643563 := by
    simpa [prefixWord, tailWord_643563, baseEnd_643563] using wordTrace_append hprefix tailTrace_643563
  have hstable : (prefixWord ++ tailWord_643563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643563).length < 2 ^ (prefixWord ++ tailWord_643563).sum := by decide
  have hdescent : baseEnd_643563 < baseStart_643563 := by decide
  rcases family_descends (prefixWord ++ tailWord_643563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643586 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_643586 : Nat := 118140960795 + 643586 * 2 ^ 59
def prefixEnd_643586 : Nat := 4983230072969 + 3 ^ 40 * 643586 * 2
def baseEnd_643586 : Nat := 146875093557610755784537

theorem tailTrace_643586 : CollatzResearch.WordTrace tailWord_643586 prefixEnd_643586 146875093557610755784537 := by
  unfold tailWord_643586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5868377461601328145767653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15649006564270208388713741 5868377461601328145767653)
  ·
    refine ⟨1100320774050249027331435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5868377461601328145767653 1100320774050249027331435)
    ·
      refine ⟨1650481161075373540997153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100320774050249027331435 1650481161075373540997153)
      ·
        refine ⟨1237860870806530155747865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1650481161075373540997153 1237860870806530155747865)
        ·
          refine ⟨928395653104897616810899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1237860870806530155747865 928395653104897616810899)
          ·
            refine ⟨1392593479657346425216349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928395653104897616810899 1392593479657346425216349)
            ·
              refine ⟨522222554871504909456131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1392593479657346425216349 522222554871504909456131)
              ·
                refine ⟨783333832307257364184197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522222554871504909456131 783333832307257364184197)
                ·
                  refine ⟨146875093557610755784537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 783333832307257364184197 146875093557610755784537)
                  ·
                    rfl

theorem cell21_643586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_643586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643586 prefixEnd_643586 := by exact prefixLift 643586
  have htrace : WordTrace (prefixWord ++ tailWord_643586) baseStart_643586 baseEnd_643586 := by
    simpa [prefixWord, tailWord_643586, baseEnd_643586] using wordTrace_append hprefix tailTrace_643586
  have hstable : (prefixWord ++ tailWord_643586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643586).length < 2 ^ (prefixWord ++ tailWord_643586).sum := by decide
  have hdescent : baseEnd_643586 < baseStart_643586 := by decide
  rcases family_descends (prefixWord ++ tailWord_643586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643645 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 4]
def baseStart_643645 : Nat := 118140960795 + 643645 * 2 ^ 59
def prefixEnd_643645 : Nat := 4983230072969 + 3 ^ 40 * 643645 * 2
def baseEnd_643645 : Nat := 146888558161439764301083

theorem tailTrace_643645 : CollatzResearch.WordTrace tailWord_643645 prefixEnd_643645 146888558161439764301083 := by
  unfold tailWord_643645
  simp only [CollatzResearch.WordTrace]
  refine ⟨23475661753191565659468389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15650441168794377106312259 23475661753191565659468389)
  ·
    refine ⟨4401686578723418561150323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23475661753191565659468389 4401686578723418561150323)
    ·
      refine ⟨6602529868085127841725485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4401686578723418561150323 6602529868085127841725485)
      ·
        refine ⟨2475948700531922940647057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6602529868085127841725485 2475948700531922940647057)
        ·
          refine ⟨1856961525398942205485293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2475948700531922940647057 1856961525398942205485293)
          ·
            refine ⟨696360572024603327056985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1856961525398942205485293 696360572024603327056985)
            ·
              refine ⟨522270429018452495292739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696360572024603327056985 522270429018452495292739)
              ·
                refine ⟨783405643527678742939109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522270429018452495292739 783405643527678742939109)
                ·
                  refine ⟨146888558161439764301083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 783405643527678742939109 146888558161439764301083)
                  ·
                    rfl

theorem cell21_643645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_643645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643645 prefixEnd_643645 := by exact prefixLift 643645
  have htrace : WordTrace (prefixWord ++ tailWord_643645) baseStart_643645 baseEnd_643645 := by
    simpa [prefixWord, tailWord_643645, baseEnd_643645] using wordTrace_append hprefix tailTrace_643645
  have hstable : (prefixWord ++ tailWord_643645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643645).length < 2 ^ (prefixWord ++ tailWord_643645).sum := by decide
  have hdescent : baseEnd_643645 < baseStart_643645 := by decide
  rcases family_descends (prefixWord ++ tailWord_643645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643715 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 7]
def baseStart_643715 : Nat := 118140960795 + 643715 * 2 ^ 59
def prefixEnd_643715 : Nat := 4983230072969 + 3 ^ 40 * 643715 * 2
def baseEnd_643715 : Nat := 146904533115135198134273

theorem tailTrace_643715 : CollatzResearch.WordTrace tailWord_643715 prefixEnd_643715 146904533115135198134273 := by
  unfold tailWord_643715
  simp only [CollatzResearch.WordTrace]
  refine ⟨23478214862937967614516599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15652143241958645076344399 23478214862937967614516599)
  ·
    refine ⟨35217322294406951421774899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23478214862937967614516599 35217322294406951421774899)
    ·
      refine ⟨52825983441610427132662349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35217322294406951421774899 52825983441610427132662349)
      ·
        refine ⟨19809743790603910174748381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52825983441610427132662349 19809743790603910174748381)
        ·
          refine ⟨7428653921476466315530643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19809743790603910174748381 7428653921476466315530643)
          ·
            refine ⟨11142980882214699473295965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7428653921476466315530643 11142980882214699473295965)
            ·
              refine ⟨4178617830830512302485987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11142980882214699473295965 4178617830830512302485987)
              ·
                refine ⟨6267926746245768453728981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178617830830512302485987 6267926746245768453728981)
                ·
                  refine ⟨146904533115135198134273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6267926746245768453728981 146904533115135198134273)
                  ·
                    rfl

theorem cell21_643715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_643715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643715 prefixEnd_643715 := by exact prefixLift 643715
  have htrace : WordTrace (prefixWord ++ tailWord_643715) baseStart_643715 baseEnd_643715 := by
    simpa [prefixWord, tailWord_643715, baseEnd_643715] using wordTrace_append hprefix tailTrace_643715
  have hstable : (prefixWord ++ tailWord_643715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643715).length < 2 ^ (prefixWord ++ tailWord_643715).sum := by decide
  have hdescent : baseEnd_643715 < baseStart_643715 := by decide
  rcases family_descends (prefixWord ++ tailWord_643715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643738 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 4]
def baseStart_643738 : Nat := 118140960795 + 643738 * 2 ^ 59
def prefixEnd_643738 : Nat := 4983230072969 + 3 ^ 40 * 643738 * 2
def baseEnd_643738 : Nat := 146909782028492269250893

theorem tailTrace_643738 : CollatzResearch.WordTrace tailWord_643738 prefixEnd_643738 146909782028492269250893 := by
  unfold tailWord_643738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5869763435463660635650967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15652702494569761695069245 5869763435463660635650967)
  ·
    refine ⟨8804645153195490953476451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5869763435463660635650967 8804645153195490953476451)
    ·
      refine ⟨13206967729793236430214677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8804645153195490953476451 13206967729793236430214677)
      ·
        refine ⟨619076612334057957666313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13206967729793236430214677 619076612334057957666313)
        ·
          refine ⟨464307459250543468249735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 619076612334057957666313 464307459250543468249735)
          ·
            refine ⟨696461188875815202374603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464307459250543468249735 696461188875815202374603)
            ·
              refine ⟨1044691783313722803561905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696461188875815202374603 1044691783313722803561905)
              ·
                refine ⟨783518837485292102671429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044691783313722803561905 783518837485292102671429)
                ·
                  refine ⟨146909782028492269250893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 783518837485292102671429 146909782028492269250893)
                  ·
                    rfl

theorem cell21_643738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_643738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643738 prefixEnd_643738 := by exact prefixLift 643738
  have htrace : WordTrace (prefixWord ++ tailWord_643738) baseStart_643738 baseEnd_643738 := by
    simpa [prefixWord, tailWord_643738, baseEnd_643738] using wordTrace_append hprefix tailTrace_643738
  have hstable : (prefixWord ++ tailWord_643738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643738).length < 2 ^ (prefixWord ++ tailWord_643738).sum := by decide
  have hdescent : baseEnd_643738 < baseStart_643738 := by decide
  rcases family_descends (prefixWord ++ tailWord_643738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643760 : List Nat := [2, 1, 1, 1, 2, 1, 3, 10]
def baseStart_643760 : Nat := 118140960795 + 643760 * 2 ^ 59
def prefixEnd_643760 : Nat := 4983230072969 + 3 ^ 40 * 643760 * 2
def baseEnd_643760 : Nat := 48971600909408373294727

theorem tailTrace_643760 : CollatzResearch.WordTrace tailWord_643760 prefixEnd_643760 48971600909408373294727 := by
  unfold tailWord_643760
  simp only [CollatzResearch.WordTrace]
  refine ⟨11739928073887470149952367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15653237431849960199936489 11739928073887470149952367)
  ·
    refine ⟨17609892110831205224928551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11739928073887470149952367 17609892110831205224928551)
    ·
      refine ⟨26414838166246807837392827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17609892110831205224928551 26414838166246807837392827)
      ·
        refine ⟨39622257249370211756089241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26414838166246807837392827 39622257249370211756089241)
        ·
          refine ⟨29716692937027658817066931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39622257249370211756089241 29716692937027658817066931)
          ·
            refine ⟨44575039405541488225600397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29716692937027658817066931 44575039405541488225600397)
            ·
              refine ⟨16715639777078058084600149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44575039405541488225600397 16715639777078058084600149)
              ·
                refine ⟨48971600909408373294727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16715639777078058084600149 48971600909408373294727)
                ·
                  rfl

theorem cell21_643760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_643760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643760 prefixEnd_643760 := by exact prefixLift 643760
  have htrace : WordTrace (prefixWord ++ tailWord_643760) baseStart_643760 baseEnd_643760 := by
    simpa [prefixWord, tailWord_643760, baseEnd_643760] using wordTrace_append hprefix tailTrace_643760
  have hstable : (prefixWord ++ tailWord_643760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643760).length < 2 ^ (prefixWord ++ tailWord_643760).sum := by decide
  have hdescent : baseEnd_643760 < baseStart_643760 := by decide
  rcases family_descends (prefixWord ++ tailWord_643760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643794 : List Nat := [3, 2, 2, 2, 3, 2, 7]
def baseStart_643794 : Nat := 118140960795 + 643794 * 2 ^ 59
def prefixEnd_643794 : Nat := 4983230072969 + 3 ^ 40 * 643794 * 2
def baseEnd_643794 : Nat := 16324729110160957368605

theorem tailTrace_643794 : CollatzResearch.WordTrace tailWord_643794 prefixEnd_643794 16324729110160957368605 := by
  unfold tailWord_643794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5870274057412941026660609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15654064153101176071094957 5870274057412941026660609)
  ·
    refine ⟨4402705543059705769995457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5870274057412941026660609 4402705543059705769995457)
    ·
      refine ⟨3302029157294779327496593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4402705543059705769995457 3302029157294779327496593)
      ·
        refine ⟨2476521867971084495622445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3302029157294779327496593 2476521867971084495622445)
        ·
          refine ⟨928695700489156685858417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2476521867971084495622445 928695700489156685858417)
          ·
            refine ⟨696521775366867514393813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928695700489156685858417 696521775366867514393813)
            ·
              refine ⟨16324729110160957368605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 696521775366867514393813 16324729110160957368605)
              ·
                rfl

theorem cell21_643794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 7].length) (baseStart_643794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643794 prefixEnd_643794 := by exact prefixLift 643794
  have htrace : WordTrace (prefixWord ++ tailWord_643794) baseStart_643794 baseEnd_643794 := by
    simpa [prefixWord, tailWord_643794, baseEnd_643794] using wordTrace_append hprefix tailTrace_643794
  have hstable : (prefixWord ++ tailWord_643794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643794).length < 2 ^ (prefixWord ++ tailWord_643794).sum := by decide
  have hdescent : baseEnd_643794 < baseStart_643794 := by decide
  rcases family_descends (prefixWord ++ tailWord_643794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643912 : List Nat := [2, 1, 3, 1, 1, 3, 10]
def baseStart_643912 : Nat := 118140960795 + 643912 * 2 ^ 59
def prefixEnd_643912 : Nat := 4983230072969 + 3 ^ 40 * 643912 * 2
def baseEnd_643912 : Nat := 16327721244345181483393

theorem tailTrace_643912 : CollatzResearch.WordTrace tailWord_643912 prefixEnd_643912 16327721244345181483393 := by
  unfold tailWord_643912
  simp only [CollatzResearch.WordTrace]
  refine ⟨11742700021612135129718995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15656933362149513506291993 11742700021612135129718995)
  ·
    refine ⟨17614050032418202694578493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11742700021612135129718995 17614050032418202694578493)
    ·
      refine ⟨6605268762156826010466935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17614050032418202694578493 6605268762156826010466935)
      ·
        refine ⟨9907903143235239015700403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6605268762156826010466935 9907903143235239015700403)
        ·
          refine ⟨14861854714852858523550605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9907903143235239015700403 14861854714852858523550605)
          ·
            refine ⟨5573195518069821946331477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14861854714852858523550605 5573195518069821946331477)
            ·
              refine ⟨16327721244345181483393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5573195518069821946331477 16327721244345181483393)
              ·
                rfl

theorem cell21_643912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 10].length) (baseStart_643912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643912 prefixEnd_643912 := by exact prefixLift 643912
  have htrace : WordTrace (prefixWord ++ tailWord_643912) baseStart_643912 baseEnd_643912 := by
    simpa [prefixWord, tailWord_643912, baseEnd_643912] using wordTrace_append hprefix tailTrace_643912
  have hstable : (prefixWord ++ tailWord_643912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643912).length < 2 ^ (prefixWord ++ tailWord_643912).sum := by decide
  have hdescent : baseEnd_643912 < baseStart_643912 := by decide
  rcases family_descends (prefixWord ++ tailWord_643912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643960 : List Nat := [2, 1, 2, 1, 1, 1, 1, 9, 3]
def baseStart_643960 : Nat := 118140960795 + 643960 * 2 ^ 59
def prefixEnd_643960 : Nat := 4983230072969 + 3 ^ 40 * 643960 * 2
def baseEnd_643960 : Nat := 146960445453069216550439

theorem tailTrace_643960 : CollatzResearch.WordTrace tailWord_643960 prefixEnd_643960 146960445453069216550439 := by
  unfold tailWord_643960
  simp only [CollatzResearch.WordTrace]
  refine ⟨11743575373525187228592667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15658100498033582971456889 11743575373525187228592667)
  ·
    refine ⟨17615363060287780842889001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11743575373525187228592667 17615363060287780842889001)
    ·
      refine ⟨13211522295215835632166751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17615363060287780842889001 13211522295215835632166751)
      ·
        refine ⟨19817283442823753448250127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13211522295215835632166751 19817283442823753448250127)
        ·
          refine ⟨29725925164235630172375191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19817283442823753448250127 29725925164235630172375191)
          ·
            refine ⟨44588887746353445258562787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29725925164235630172375191 44588887746353445258562787)
            ·
              refine ⟨66883331619530167887844181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44588887746353445258562787 66883331619530167887844181)
              ·
                refine ⟨391894521208184577467837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 66883331619530167887844181 391894521208184577467837)
                ·
                  refine ⟨146960445453069216550439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391894521208184577467837 146960445453069216550439)
                  ·
                    rfl

theorem cell21_643960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 3].length) (baseStart_643960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643960 prefixEnd_643960 := by exact prefixLift 643960
  have htrace : WordTrace (prefixWord ++ tailWord_643960) baseStart_643960 baseEnd_643960 := by
    simpa [prefixWord, tailWord_643960, baseEnd_643960] using wordTrace_append hprefix tailTrace_643960
  have hstable : (prefixWord ++ tailWord_643960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643960).length < 2 ^ (prefixWord ++ tailWord_643960).sum := by decide
  have hdescent : baseEnd_643960 < baseStart_643960 := by decide
  rcases family_descends (prefixWord ++ tailWord_643960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644129 : List Nat := [1, 2, 3, 2, 3, 1, 3, 3, 3]
def baseStart_644129 : Nat := 118140960795 + 644129 * 2 ^ 59
def prefixEnd_644129 : Nat := 4983230072969 + 3 ^ 40 * 644129 * 2
def baseEnd_644129 : Nat := 146999013555562478233427

theorem tailTrace_644129 : CollatzResearch.WordTrace tailWord_644129 prefixEnd_644129 146999013555562478233427 := by
  unfold tailWord_644129
  simp only [CollatzResearch.WordTrace]
  refine ⟨23493314683438116320087441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15662209788958744213391627 23493314683438116320087441)
  ·
    refine ⟨17619986012578587240065581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23493314683438116320087441 17619986012578587240065581)
    ·
      refine ⟨6607494754716970215024593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17619986012578587240065581 6607494754716970215024593)
      ·
        refine ⟨4955621066037727661268445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6607494754716970215024593 4955621066037727661268445)
        ·
          refine ⟨1858357899764147872975667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4955621066037727661268445 1858357899764147872975667)
          ·
            refine ⟨2787536849646221809463501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858357899764147872975667 2787536849646221809463501)
            ·
              refine ⟨1045326318617333178548813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2787536849646221809463501 1045326318617333178548813)
              ·
                refine ⟨391997369481499941955805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1045326318617333178548813 391997369481499941955805)
                ·
                  refine ⟨146999013555562478233427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391997369481499941955805 146999013555562478233427)
                  ·
                    rfl

theorem cell21_644129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 3].length) (baseStart_644129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644129 prefixEnd_644129 := by exact prefixLift 644129
  have htrace : WordTrace (prefixWord ++ tailWord_644129) baseStart_644129 baseEnd_644129 := by
    simpa [prefixWord, tailWord_644129, baseEnd_644129] using wordTrace_append hprefix tailTrace_644129
  have hstable : (prefixWord ++ tailWord_644129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644129).length < 2 ^ (prefixWord ++ tailWord_644129).sum := by decide
  have hdescent : baseEnd_644129 < baseStart_644129 := by decide
  rcases family_descends (prefixWord ++ tailWord_644129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644157 : List Nat := [1, 4, 1, 3, 1, 3, 2, 6]
def baseStart_644157 : Nat := 118140960795 + 644157 * 2 ^ 59
def prefixEnd_644157 : Nat := 4983230072969 + 3 ^ 40 * 644157 * 2
def baseEnd_644157 : Nat := 49001801179013550588901

theorem tailTrace_644157 : CollatzResearch.WordTrace tailWord_644157 prefixEnd_644157 49001801179013550588901 := by
  unfold tailWord_644157
  simp only [CollatzResearch.WordTrace]
  refine ⟨23494335927336677102106725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15662890618224451401404483 23494335927336677102106725)
  ·
    refine ⟨4405187986375626956645011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23494335927336677102106725 4405187986375626956645011)
    ·
      refine ⟨6607781979563440434967517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4405187986375626956645011 6607781979563440434967517)
      ·
        refine ⟨2477918242336290163112819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6607781979563440434967517 2477918242336290163112819)
        ·
          refine ⟨3716877363504435244669229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2477918242336290163112819 3716877363504435244669229)
          ·
            refine ⟨1393829011314163216750961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3716877363504435244669229 1393829011314163216750961)
            ·
              refine ⟨1045371758485622412563221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1393829011314163216750961 1045371758485622412563221)
              ·
                refine ⟨49001801179013550588901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1045371758485622412563221 49001801179013550588901)
                ·
                  rfl

theorem cell21_644157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 6].length) (baseStart_644157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644157 prefixEnd_644157 := by exact prefixLift 644157
  have htrace : WordTrace (prefixWord ++ tailWord_644157) baseStart_644157 baseEnd_644157 := by
    simpa [prefixWord, tailWord_644157, baseEnd_644157] using wordTrace_append hprefix tailTrace_644157
  have hstable : (prefixWord ++ tailWord_644157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644157).length < 2 ^ (prefixWord ++ tailWord_644157).sum := by decide
  have hdescent : baseEnd_644157 < baseStart_644157 := by decide
  rcases family_descends (prefixWord ++ tailWord_644157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644185 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 6]
def baseStart_644185 : Nat := 118140960795 + 644185 * 2 ^ 59
def prefixEnd_644185 : Nat := 4983230072969 + 3 ^ 40 * 644185 * 2
def baseEnd_644185 : Nat := 147011793518518825299979

theorem tailTrace_644185 : CollatzResearch.WordTrace tailWord_644185 prefixEnd_644185 147011793518518825299979 := by
  unfold tailWord_644185
  simp only [CollatzResearch.WordTrace]
  refine ⟨23495357171235237884126009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15663571447490158589417339 23495357171235237884126009)
  ·
    refine ⟨17621517878426428413094507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23495357171235237884126009 17621517878426428413094507)
    ·
      refine ⟨26432276817639642619641761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17621517878426428413094507 26432276817639642619641761)
      ·
        refine ⟨19824207613229731964731321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26432276817639642619641761 19824207613229731964731321)
        ·
          refine ⟨14868155709922298973548491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19824207613229731964731321 14868155709922298973548491)
          ·
            refine ⟨22302233564883448460322737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14868155709922298973548491 22302233564883448460322737)
            ·
              refine ⟨16726675173662586345242053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22302233564883448460322737 16726675173662586345242053)
              ·
                refine ⟨3136251595061734939732885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16726675173662586345242053 3136251595061734939732885)
                ·
                  refine ⟨147011793518518825299979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3136251595061734939732885 147011793518518825299979)
                  ·
                    rfl

theorem cell21_644185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_644185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644185 prefixEnd_644185 := by exact prefixLift 644185
  have htrace : WordTrace (prefixWord ++ tailWord_644185) baseStart_644185 baseEnd_644185 := by
    simpa [prefixWord, tailWord_644185, baseEnd_644185] using wordTrace_append hprefix tailTrace_644185
  have hstable : (prefixWord ++ tailWord_644185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644185).length < 2 ^ (prefixWord ++ tailWord_644185).sum := by decide
  have hdescent : baseEnd_644185 < baseStart_644185 := by decide
  rcases family_descends (prefixWord ++ tailWord_644185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644205 : List Nat := [1, 5, 1, 1, 2, 3, 1, 4, 3]
def baseStart_644205 : Nat := 118140960795 + 644205 * 2 ^ 59
def prefixEnd_644205 : Nat := 4983230072969 + 3 ^ 40 * 644205 * 2
def baseEnd_644205 : Nat := 147016357791003234966605

theorem tailTrace_644205 : CollatzResearch.WordTrace tailWord_644205 prefixEnd_644205 147016357791003234966605 := by
  unfold tailWord_644205
  simp only [CollatzResearch.WordTrace]
  refine ⟨23496086631162781299854069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15664057754108520866569379 23496086631162781299854069)
  ·
    refine ⟨2202758121671510746861319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23496086631162781299854069 2202758121671510746861319)
    ·
      refine ⟨3304137182507266120291979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202758121671510746861319 3304137182507266120291979)
      ·
        refine ⟨4956205773760899180437969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3304137182507266120291979 4956205773760899180437969)
        ·
          refine ⟨3717154330320674385328477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4956205773760899180437969 3717154330320674385328477)
          ·
            refine ⟨1393932873870252894498179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3717154330320674385328477 1393932873870252894498179)
            ·
              refine ⟨2090899310805379341747269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393932873870252894498179 2090899310805379341747269)
              ·
                refine ⟨392043620776008626577613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2090899310805379341747269 392043620776008626577613)
                ·
                  refine ⟨147016357791003234966605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392043620776008626577613 147016357791003234966605)
                  ·
                    rfl

theorem cell21_644205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_644205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644205 prefixEnd_644205 := by exact prefixLift 644205
  have htrace : WordTrace (prefixWord ++ tailWord_644205) baseStart_644205 baseEnd_644205 := by
    simpa [prefixWord, tailWord_644205, baseEnd_644205] using wordTrace_append hprefix tailTrace_644205
  have hstable : (prefixWord ++ tailWord_644205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644205).length < 2 ^ (prefixWord ++ tailWord_644205).sum := by decide
  have hdescent : baseEnd_644205 < baseStart_644205 := by decide
  rcases family_descends (prefixWord ++ tailWord_644205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644216 : List Nat := [2, 1, 2, 1, 1, 1, 7, 6]
def baseStart_644216 : Nat := 118140960795 + 644216 * 2 ^ 59
def prefixEnd_644216 : Nat := 4983230072969 + 3 ^ 40 * 644216 * 2
def baseEnd_644216 : Nat := 49006289380289886761083

theorem tailTrace_644216 : CollatzResearch.WordTrace tailWord_644216 prefixEnd_644216 49006289380289886761083 := by
  unfold tailWord_644216
  simp only [CollatzResearch.WordTrace]
  refine ⟨11748243917061465089252251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15664325222748620119003001 11748243917061465089252251)
  ·
    refine ⟨17622365875592197633878377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11748243917061465089252251 17622365875592197633878377)
    ·
      refine ⟨13216774406694148225408783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17622365875592197633878377 13216774406694148225408783)
      ·
        refine ⟨19825161610041222338113175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13216774406694148225408783 19825161610041222338113175)
        ·
          refine ⟨29737742415061833507169763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19825161610041222338113175 29737742415061833507169763)
          ·
            refine ⟨44606613622592750260754645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29737742415061833507169763 44606613622592750260754645)
            ·
              refine ⟨1045467506779517584236437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 44606613622592750260754645 1045467506779517584236437)
              ·
                refine ⟨49006289380289886761083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1045467506779517584236437 49006289380289886761083)
                ·
                  rfl

theorem cell21_644216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_644216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644216 prefixEnd_644216 := by exact prefixLift 644216
  have htrace : WordTrace (prefixWord ++ tailWord_644216) baseStart_644216 baseEnd_644216 := by
    simpa [prefixWord, tailWord_644216, baseEnd_644216] using wordTrace_append hprefix tailTrace_644216
  have hstable : (prefixWord ++ tailWord_644216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644216).length < 2 ^ (prefixWord ++ tailWord_644216).sum := by decide
  have hdescent : baseEnd_644216 < baseStart_644216 := by decide
  rcases family_descends (prefixWord ++ tailWord_644216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644233 : List Nat := [1, 2, 1, 1, 4, 4, 3, 5]
def baseStart_644233 : Nat := 118140960795 + 644233 * 2 ^ 59
def prefixEnd_644233 : Nat := 4983230072969 + 3 ^ 40 * 644233 * 2
def baseEnd_644233 : Nat := 49007582590827136166627

theorem tailTrace_644233 : CollatzResearch.WordTrace tailWord_644233 prefixEnd_644233 49007582590827136166627 := by
  unfold tailWord_644233
  simp only [CollatzResearch.WordTrace]
  refine ⟨23497107875061342081873353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15664738583374228054582235 23497107875061342081873353)
  ·
    refine ⟨17622830906296006561405015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23497107875061342081873353 17622830906296006561405015)
    ·
      refine ⟨26434246359444009842107523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17622830906296006561405015 26434246359444009842107523)
      ·
        refine ⟨39651369539166014763161285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26434246359444009842107523 39651369539166014763161285)
        ·
          refine ⟨7434631788593627768092741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39651369539166014763161285 7434631788593627768092741)
          ·
            refine ⟨1393993460361305206517389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7434631788593627768092741 1393993460361305206517389)
            ·
              refine ⟨522747547635489452444021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1393993460361305206517389 522747547635489452444021)
              ·
                refine ⟨49007582590827136166627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 522747547635489452444021 49007582590827136166627)
                ·
                  rfl

theorem cell21_644233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 5].length) (baseStart_644233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644233 prefixEnd_644233 := by exact prefixLift 644233
  have htrace : WordTrace (prefixWord ++ tailWord_644233) baseStart_644233 baseEnd_644233 := by
    simpa [prefixWord, tailWord_644233, baseEnd_644233] using wordTrace_append hprefix tailTrace_644233
  have hstable : (prefixWord ++ tailWord_644233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644233).length < 2 ^ (prefixWord ++ tailWord_644233).sum := by decide
  have hdescent : baseEnd_644233 < baseStart_644233 := by decide
  rcases family_descends (prefixWord ++ tailWord_644233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644309 : List Nat := [1, 3, 2, 4, 1, 3, 7]
def baseStart_644309 : Nat := 118140960795 + 644309 * 2 ^ 59
def prefixEnd_644309 : Nat := 4983230072969 + 3 ^ 40 * 644309 * 2
def baseEnd_644309 : Nat := 16337788000880240581451

theorem tailTrace_644309 : CollatzResearch.WordTrace tailWord_644309 prefixEnd_644309 16337788000880240581451 := by
  unfold tailWord_644309
  simp only [CollatzResearch.WordTrace]
  refine ⟨23499879822786007061639981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15666586548524004707759987 23499879822786007061639981)
  ·
    refine ⟨8812454933544752648114993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23499879822786007061639981 8812454933544752648114993)
    ·
      refine ⟨6609341200158564486086245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8812454933544752648114993 6609341200158564486086245)
      ·
        refine ⟨1239251475029730841141171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6609341200158564486086245 1239251475029730841141171)
        ·
          refine ⟨1858877212544596261711757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239251475029730841141171 1858877212544596261711757)
          ·
            refine ⟨697078954704223598141909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1858877212544596261711757 697078954704223598141909)
            ·
              refine ⟨16337788000880240581451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 697078954704223598141909 16337788000880240581451)
              ·
                rfl

theorem cell21_644309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 7].length) (baseStart_644309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644309 prefixEnd_644309 := by exact prefixLift 644309
  have htrace : WordTrace (prefixWord ++ tailWord_644309) baseStart_644309 baseEnd_644309 := by
    simpa [prefixWord, tailWord_644309, baseEnd_644309] using wordTrace_append hprefix tailTrace_644309
  have hstable : (prefixWord ++ tailWord_644309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644309).length < 2 ^ (prefixWord ++ tailWord_644309).sum := by decide
  have hdescent : baseEnd_644309 < baseStart_644309 := by decide
  rcases family_descends (prefixWord ++ tailWord_644309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644416 : List Nat := [2, 1, 1, 2, 2, 1, 6, 3, 3]
def baseStart_644416 : Nat := 118140960795 + 644416 * 2 ^ 59
def prefixEnd_644416 : Nat := 4983230072969 + 3 ^ 40 * 644416 * 2
def baseEnd_644416 : Nat := 147064510865713756949507

theorem tailTrace_644416 : CollatzResearch.WordTrace tailWord_644416 prefixEnd_644416 147064510865713756949507 := by
  unfold tailWord_644416
  simp only [CollatzResearch.WordTrace]
  refine ⟨11751891216699182167892551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15669188288932242890523401 11751891216699182167892551)
  ·
    refine ⟨17627836825048773251838827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11751891216699182167892551 17627836825048773251838827)
    ·
      refine ⟨26441755237573159877758241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17627836825048773251838827 26441755237573159877758241)
      ·
        refine ⟨19831316428179869908318681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26441755237573159877758241 19831316428179869908318681)
        ·
          refine ⟨14873487321134902431239011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19831316428179869908318681 14873487321134902431239011)
          ·
            refine ⟨22310230981702353646858517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14873487321134902431239011 22310230981702353646858517)
            ·
              refine ⟨1045792077267297827196493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22310230981702353646858517 1045792077267297827196493)
              ·
                refine ⟨392172028975236685198685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1045792077267297827196493 392172028975236685198685)
                ·
                  refine ⟨147064510865713756949507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392172028975236685198685 147064510865713756949507)
                  ·
                    rfl

theorem cell21_644416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 3].length) (baseStart_644416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644416 prefixEnd_644416 := by exact prefixLift 644416
  have htrace : WordTrace (prefixWord ++ tailWord_644416) baseStart_644416 baseEnd_644416 := by
    simpa [prefixWord, tailWord_644416, baseEnd_644416] using wordTrace_append hprefix tailTrace_644416
  have hstable : (prefixWord ++ tailWord_644416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644416).length < 2 ^ (prefixWord ++ tailWord_644416).sum := by decide
  have hdescent : baseEnd_644416 < baseStart_644416 := by decide
  rcases family_descends (prefixWord ++ tailWord_644416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644422 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_644422 : Nat := 118140960795 + 644422 * 2 ^ 59
def prefixEnd_644422 : Nat := 4983230072969 + 3 ^ 40 * 644422 * 2
def baseEnd_644422 : Nat := 147065880147459079849495

theorem tailTrace_644422 : CollatzResearch.WordTrace tailWord_644422 prefixEnd_644422 147065880147459079849495 := by
  unfold tailWord_644422
  simp only [CollatzResearch.WordTrace]
  refine ⟨734500039730519605015735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15669334180917751573669013 734500039730519605015735)
  ·
    refine ⟨1101750059595779407523603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 734500039730519605015735 1101750059595779407523603)
    ·
      refine ⟨1652625089393669111285405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1101750059595779407523603 1652625089393669111285405)
      ·
        refine ⟨619734408522625916732027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1652625089393669111285405 619734408522625916732027)
        ·
          refine ⟨929601612783938875098041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619734408522625916732027 929601612783938875098041)
          ·
            refine ⟨697201209587954156323531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929601612783938875098041 697201209587954156323531)
            ·
              refine ⟨1045801814381931234485297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697201209587954156323531 1045801814381931234485297)
              ·
                refine ⟨784351360786448425863973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045801814381931234485297 784351360786448425863973)
                ·
                  refine ⟨147065880147459079849495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 784351360786448425863973 147065880147459079849495)
                  ·
                    rfl

theorem cell21_644422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_644422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644422 prefixEnd_644422 := by exact prefixLift 644422
  have htrace : WordTrace (prefixWord ++ tailWord_644422) baseStart_644422 baseEnd_644422 := by
    simpa [prefixWord, tailWord_644422, baseEnd_644422] using wordTrace_append hprefix tailTrace_644422
  have hstable : (prefixWord ++ tailWord_644422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644422).length < 2 ^ (prefixWord ++ tailWord_644422).sum := by decide
  have hdescent : baseEnd_644422 < baseStart_644422 := by decide
  rcases family_descends (prefixWord ++ tailWord_644422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644461 : List Nat := [1, 5, 1, 1, 1, 3, 4, 5]
def baseStart_644461 : Nat := 118140960795 + 644461 * 2 ^ 59
def prefixEnd_644461 : Nat := 4983230072969 + 3 ^ 40 * 644461 * 2
def baseEnd_644461 : Nat := 49024926826267892899805

theorem tailTrace_644461 : CollatzResearch.WordTrace tailWord_644461 prefixEnd_644461 49024926826267892899805 := by
  unfold tailWord_644461
  simp only [CollatzResearch.WordTrace]
  refine ⟨23505423718235337021173237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15670282478823558014115491 23505423718235337021173237)
  ·
    refine ⟨2203633473584562845734991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23505423718235337021173237 2203633473584562845734991)
    ·
      refine ⟨3305450210376844268602487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203633473584562845734991 3305450210376844268602487)
      ·
        refine ⟨4958175315565266402903731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305450210376844268602487 4958175315565266402903731)
        ·
          refine ⟨7437262973347899604355597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4958175315565266402903731 7437262973347899604355597)
          ·
            refine ⟨2788973615005462351633349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7437262973347899604355597 2788973615005462351633349)
            ·
              refine ⟨522932552813524190931253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2788973615005462351633349 522932552813524190931253)
              ·
                refine ⟨49024926826267892899805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 522932552813524190931253 49024926826267892899805)
                ·
                  rfl

theorem cell21_644461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 5].length) (baseStart_644461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644461 prefixEnd_644461 := by exact prefixLift 644461
  have htrace : WordTrace (prefixWord ++ tailWord_644461) baseStart_644461 baseEnd_644461 := by
    simpa [prefixWord, tailWord_644461, baseEnd_644461] using wordTrace_append hprefix tailTrace_644461
  have hstable : (prefixWord ++ tailWord_644461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644461).length < 2 ^ (prefixWord ++ tailWord_644461).sum := by decide
  have hdescent : baseEnd_644461 < baseStart_644461 := by decide
  rcases family_descends (prefixWord ++ tailWord_644461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644498 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 4]
def baseStart_644498 : Nat := 118140960795 + 644498 * 2 ^ 59
def prefixEnd_644498 : Nat := 4983230072969 + 3 ^ 40 * 644498 * 2
def baseEnd_644498 : Nat := 147083224382899836582673

theorem tailTrace_644498 : CollatzResearch.WordTrace tailWord_644498 prefixEnd_644498 147083224382899836582673 := by
  unfold tailWord_644498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5876693304775323085067537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15671182146067528226846765 5876693304775323085067537)
  ·
    refine ⟨4407519978581492313800653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5876693304775323085067537 4407519978581492313800653)
    ·
      refine ⟨1652819991968059617675245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4407519978581492313800653 1652819991968059617675245)
      ·
        refine ⟨619807496988022356628217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1652819991968059617675245 619807496988022356628217)
        ·
          refine ⟨464855622741016767471163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 619807496988022356628217 464855622741016767471163)
          ·
            refine ⟨697283434111525151206745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464855622741016767471163 697283434111525151206745)
            ·
              refine ⟨522962575583643863405059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697283434111525151206745 522962575583643863405059)
              ·
                refine ⟨784443863375465795107589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522962575583643863405059 784443863375465795107589)
                ·
                  refine ⟨147083224382899836582673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 784443863375465795107589 147083224382899836582673)
                  ·
                    rfl

theorem cell21_644498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_644498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644498 prefixEnd_644498 := by exact prefixLift 644498
  have htrace : WordTrace (prefixWord ++ tailWord_644498) baseStart_644498 baseEnd_644498 := by
    simpa [prefixWord, tailWord_644498, baseEnd_644498] using wordTrace_append hprefix tailTrace_644498
  have hstable : (prefixWord ++ tailWord_644498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644498).length < 2 ^ (prefixWord ++ tailWord_644498).sum := by decide
  have hdescent : baseEnd_644498 < baseStart_644498 := by decide
  rcases family_descends (prefixWord ++ tailWord_644498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644506 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_644506 : Nat := 118140960795 + 644506 * 2 ^ 59
def prefixEnd_644506 : Nat := 4983230072969 + 3 ^ 40 * 644506 * 2
def baseEnd_644506 : Nat := 147085050091893600449323

theorem tailTrace_644506 : CollatzResearch.WordTrace tailWord_644506 prefixEnd_644506 147085050091893600449323 := by
  unfold tailWord_644506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5876766250768077426640343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15671376668714873137707581 5876766250768077426640343)
  ·
    refine ⟨8815149376152116139960515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5876766250768077426640343 8815149376152116139960515)
    ·
      refine ⟨13222724064228174209940773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8815149376152116139960515 13222724064228174209940773)
      ·
        refine ⟨2479260762042782664363895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13222724064228174209940773 2479260762042782664363895)
        ·
          refine ⟨3718891143064173996545843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2479260762042782664363895 3718891143064173996545843)
          ·
            refine ⟨5578336714596260994818765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718891143064173996545843 5578336714596260994818765)
            ·
              refine ⟨2091876267973597873057037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5578336714596260994818765 2091876267973597873057037)
              ·
                refine ⟨784453600490099202396389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2091876267973597873057037 784453600490099202396389)
                ·
                  refine ⟨147085050091893600449323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 784453600490099202396389 147085050091893600449323)
                  ·
                    rfl

theorem cell21_644506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_644506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644506 prefixEnd_644506 := by exact prefixLift 644506
  have htrace : WordTrace (prefixWord ++ tailWord_644506) baseStart_644506 baseEnd_644506 := by
    simpa [prefixWord, tailWord_644506, baseEnd_644506] using wordTrace_append hprefix tailTrace_644506
  have hstable : (prefixWord ++ tailWord_644506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644506).length < 2 ^ (prefixWord ++ tailWord_644506).sum := by decide
  have hdescent : baseEnd_644506 < baseStart_644506 := by decide
  rcases family_descends (prefixWord ++ tailWord_644506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644641 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 6]
def baseStart_644641 : Nat := 118140960795 + 644641 * 2 ^ 59
def prefixEnd_644641 : Nat := 4983230072969 + 3 ^ 40 * 644641 * 2
def baseEnd_644641 : Nat := 147115858931163365699047

theorem tailTrace_644641 : CollatzResearch.WordTrace tailWord_644641 prefixEnd_644641 147115858931163365699047 := by
  unfold tailWord_644641
  simp only [CollatzResearch.WordTrace]
  refine ⟨23511988857583227762725777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15674659238388818508483851 23511988857583227762725777)
  ·
    refine ⟨17633991643187420822044333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23511988857583227762725777 17633991643187420822044333)
    ·
      refine ⟨6612746866195282808266625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17633991643187420822044333 6612746866195282808266625)
      ·
        refine ⟨4959560149646462106199969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6612746866195282808266625 4959560149646462106199969)
        ·
          refine ⟨3719670112234846579649977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4959560149646462106199969 3719670112234846579649977)
          ·
            refine ⟨2789752584176134934737483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3719670112234846579649977 2789752584176134934737483)
            ·
              refine ⟨4184628876264202402106225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789752584176134934737483 4184628876264202402106225)
              ·
                refine ⟨3138471657198151801579669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4184628876264202402106225 3138471657198151801579669)
                ·
                  refine ⟨147115858931163365699047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3138471657198151801579669 147115858931163365699047)
                  ·
                    rfl

theorem cell21_644641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_644641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644641 prefixEnd_644641 := by exact prefixLift 644641
  have htrace : WordTrace (prefixWord ++ tailWord_644641) baseStart_644641 baseEnd_644641 := by
    simpa [prefixWord, tailWord_644641, baseEnd_644641] using wordTrace_append hprefix tailTrace_644641
  have hstable : (prefixWord ++ tailWord_644641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644641).length < 2 ^ (prefixWord ++ tailWord_644641).sum := by decide
  have hdescent : baseEnd_644641 < baseStart_644641 := by decide
  rcases family_descends (prefixWord ++ tailWord_644641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644661 : List Nat := [1, 3, 3, 1, 1, 4, 3, 2, 3]
def baseStart_644661 : Nat := 118140960795 + 644661 * 2 ^ 59
def prefixEnd_644661 : Nat := 4983230072969 + 3 ^ 40 * 644661 * 2
def baseEnd_644661 : Nat := 147120423203647775365673

theorem tailTrace_644661 : CollatzResearch.WordTrace tailWord_644661 prefixEnd_644661 147120423203647775365673 := by
  unfold tailWord_644661
  simp only [CollatzResearch.WordTrace]
  refine ⟨23512718317510771178453837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15675145545007180785635891 23512718317510771178453837)
  ·
    refine ⟨8817269369066539191920189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23512718317510771178453837 8817269369066539191920189)
    ·
      refine ⟨3306476013399952196970071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8817269369066539191920189 3306476013399952196970071)
      ·
        refine ⟨4959714020099928295455107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3306476013399952196970071 4959714020099928295455107)
        ·
          refine ⟨7439571030149892443182661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4959714020099928295455107 7439571030149892443182661)
          ·
            refine ⟨1394919568153104833096749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7439571030149892443182661 1394919568153104833096749)
            ·
              refine ⟨523094838057414312411281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1394919568153104833096749 523094838057414312411281)
              ·
                refine ⟨392321128543060734308461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523094838057414312411281 392321128543060734308461)
                ·
                  refine ⟨147120423203647775365673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392321128543060734308461 147120423203647775365673)
                  ·
                    rfl

theorem cell21_644661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_644661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644661 prefixEnd_644661 := by exact prefixLift 644661
  have htrace : WordTrace (prefixWord ++ tailWord_644661) baseStart_644661 baseEnd_644661 := by
    simpa [prefixWord, tailWord_644661, baseEnd_644661] using wordTrace_append hprefix tailTrace_644661
  have hstable : (prefixWord ++ tailWord_644661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644661).length < 2 ^ (prefixWord ++ tailWord_644661).sum := by decide
  have hdescent : baseEnd_644661 < baseStart_644661 := by decide
  rcases family_descends (prefixWord ++ tailWord_644661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644686 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_644686 : Nat := 118140960795 + 644686 * 2 ^ 59
def prefixEnd_644686 : Nat := 4983230072969 + 3 ^ 40 * 644686 * 2
def baseEnd_644686 : Nat := 147126128544253287448955

theorem tailTrace_644686 : CollatzResearch.WordTrace tailWord_644686 prefixEnd_644686 147126128544253287448955 := by
  unfold tailWord_644686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939203767802525056014239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15675753428280133632075941 2939203767802525056014239)
  ·
    refine ⟨4408805651703787584021359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2939203767802525056014239 4408805651703787584021359)
    ·
      refine ⟨6613208477555681376032039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4408805651703787584021359 6613208477555681376032039)
      ·
        refine ⟨9919812716333522064048059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6613208477555681376032039 9919812716333522064048059)
        ·
          refine ⟨14879719074500283096072089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9919812716333522064048059 14879719074500283096072089)
          ·
            refine ⟨11159789305875212322054067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14879719074500283096072089 11159789305875212322054067)
            ·
              refine ⟨16739683958812818483081101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11159789305875212322054067 16739683958812818483081101)
              ·
                refine ⟨6277381484554806931155413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16739683958812818483081101 6277381484554806931155413)
                ·
                  refine ⟨147126128544253287448955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6277381484554806931155413 147126128544253287448955)
                  ·
                    rfl

theorem cell21_644686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_644686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644686 prefixEnd_644686 := by exact prefixLift 644686
  have htrace : WordTrace (prefixWord ++ tailWord_644686) baseStart_644686 baseEnd_644686 := by
    simpa [prefixWord, tailWord_644686, baseEnd_644686] using wordTrace_append hprefix tailTrace_644686
  have hstable : (prefixWord ++ tailWord_644686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644686).length < 2 ^ (prefixWord ++ tailWord_644686).sum := by decide
  have hdescent : baseEnd_644686 < baseStart_644686 := by decide
  rcases family_descends (prefixWord ++ tailWord_644686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644720 : List Nat := [2, 1, 1, 1, 6, 2, 1, 4, 3]
def baseStart_644720 : Nat := 118140960795 + 644720 * 2 ^ 59
def prefixEnd_644720 : Nat := 4983230072969 + 3 ^ 40 * 644720 * 2
def baseEnd_644720 : Nat := 147133887807476783882219

theorem tailTrace_644720 : CollatzResearch.WordTrace tailWord_644720 prefixEnd_644720 147133887807476783882219 := by
  unfold tailWord_644720
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757435112148512127425807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15676580149531349503234409 11757435112148512127425807)
  ·
    refine ⟨17636152668222768191138711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11757435112148512127425807 17636152668222768191138711)
    ·
      refine ⟨26454229002334152286708067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17636152668222768191138711 26454229002334152286708067)
      ·
        refine ⟨39681343503501228430062101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26454229002334152286708067 39681343503501228430062101)
        ·
          refine ⟨1860062976726620082659161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39681343503501228430062101 1860062976726620082659161)
          ·
            refine ⟨1395047232544965061994371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1860062976726620082659161 1395047232544965061994371)
            ·
              refine ⟨2092570848817447592991557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395047232544965061994371 2092570848817447592991557)
              ·
                refine ⟨392357034153271423685917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2092570848817447592991557 392357034153271423685917)
                ·
                  refine ⟨147133887807476783882219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392357034153271423685917 147133887807476783882219)
                  ·
                    rfl

theorem cell21_644720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 3].length) (baseStart_644720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644720 prefixEnd_644720 := by exact prefixLift 644720
  have htrace : WordTrace (prefixWord ++ tailWord_644720) baseStart_644720 baseEnd_644720 := by
    simpa [prefixWord, tailWord_644720, baseEnd_644720] using wordTrace_append hprefix tailTrace_644720
  have hstable : (prefixWord ++ tailWord_644720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644720).length < 2 ^ (prefixWord ++ tailWord_644720).sum := by decide
  have hdescent : baseEnd_644720 < baseStart_644720 := by decide
  rcases family_descends (prefixWord ++ tailWord_644720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644748 : List Nat := [2, 2, 1, 2, 1, 1, 7, 5]
def baseStart_644748 : Nat := 118140960795 + 644748 * 2 ^ 59
def prefixEnd_644748 : Nat := 4983230072969 + 3 ^ 40 * 644748 * 2
def baseEnd_644748 : Nat := 49046759262984985805165

theorem tailTrace_644748 : CollatzResearch.WordTrace tailWord_644748 prefixEnd_644748 49046759262984985805165 := by
  unfold tailWord_644748
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757945734097792518435449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15677260978797056691247265 11757945734097792518435449)
  ·
    refine ⟨8818459300573344388826587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11757945734097792518435449 8818459300573344388826587)
    ·
      refine ⟨13227688950860016583239881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8818459300573344388826587 13227688950860016583239881)
      ·
        refine ⟨9920766713145012437429911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13227688950860016583239881 9920766713145012437429911)
        ·
          refine ⟨14881150069717518656144867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9920766713145012437429911 14881150069717518656144867)
          ·
            refine ⟨22321725104576277984217301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14881150069717518656144867 22321725104576277984217301)
            ·
              refine ⟨523165432138506515255093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 22321725104576277984217301 523165432138506515255093)
              ·
                refine ⟨49046759262984985805165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 523165432138506515255093 49046759262984985805165)
                ·
                  rfl

theorem cell21_644748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_644748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644748 prefixEnd_644748 := by exact prefixLift 644748
  have htrace : WordTrace (prefixWord ++ tailWord_644748) baseStart_644748 baseEnd_644748 := by
    simpa [prefixWord, tailWord_644748, baseEnd_644748] using wordTrace_append hprefix tailTrace_644748
  have hstable : (prefixWord ++ tailWord_644748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644748).length < 2 ^ (prefixWord ++ tailWord_644748).sum := by decide
  have hdescent : baseEnd_644748 < baseStart_644748 := by decide
  rcases family_descends (prefixWord ++ tailWord_644748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644793 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 4]
def baseStart_644793 : Nat := 118140960795 + 644793 * 2 ^ 59
def prefixEnd_644793 : Nat := 4983230072969 + 3 ^ 40 * 644793 * 2
def baseEnd_644793 : Nat := 147150547402044879165403

theorem tailTrace_644793 : CollatzResearch.WordTrace tailWord_644793 prefixEnd_644793 147150547402044879165403 := by
  unfold tailWord_644793
  simp only [CollatzResearch.WordTrace]
  refine ⟨23517532753032557722259033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15678355168688371814839355 23517532753032557722259033)
  ·
    refine ⟨17638149564774418291694275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23517532753032557722259033 17638149564774418291694275)
    ·
      refine ⟨26457224347161627437541413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17638149564774418291694275 26457224347161627437541413)
      ·
        refine ⟨4960729565092805144539015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26457224347161627437541413 4960729565092805144539015)
        ·
          refine ⟨7441094347639207716808523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4960729565092805144539015 7441094347639207716808523)
          ·
            refine ⟨11161641521458811575212785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7441094347639207716808523 11161641521458811575212785)
            ·
              refine ⟨8371231141094108681409589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11161641521458811575212785 8371231141094108681409589)
              ·
                refine ⟨784802919477572688882149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8371231141094108681409589 784802919477572688882149)
                ·
                  refine ⟨147150547402044879165403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 784802919477572688882149 147150547402044879165403)
                  ·
                    rfl

theorem cell21_644793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_644793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644793 prefixEnd_644793 := by exact prefixLift 644793
  have htrace : WordTrace (prefixWord ++ tailWord_644793) baseStart_644793 baseEnd_644793 := by
    simpa [prefixWord, tailWord_644793, baseEnd_644793] using wordTrace_append hprefix tailTrace_644793
  have hstable : (prefixWord ++ tailWord_644793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644793).length < 2 ^ (prefixWord ++ tailWord_644793).sum := by decide
  have hdescent : baseEnd_644793 < baseStart_644793 := by decide
  rcases family_descends (prefixWord ++ tailWord_644793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644807 : List Nat := [1, 1, 4, 1, 1, 1, 5, 7]
def baseStart_644807 : Nat := 118140960795 + 644807 * 2 ^ 59
def prefixEnd_644807 : Nat := 4983230072969 + 3 ^ 40 * 644807 * 2
def baseEnd_644807 : Nat := 49051247464261321977347

theorem tailTrace_644807 : CollatzResearch.WordTrace tailWord_644807 prefixEnd_644807 49051247464261321977347 := by
  unfold tailWord_644807
  simp only [CollatzResearch.WordTrace]
  refine ⟨23518043374981838113268675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15678695583321225408845783 23518043374981838113268675)
  ·
    refine ⟨35277065062472757169903013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23518043374981838113268675 35277065062472757169903013)
    ·
      refine ⟨6614449699213641969356815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35277065062472757169903013 6614449699213641969356815)
      ·
        refine ⟨9921674548820462954035223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6614449699213641969356815 9921674548820462954035223)
        ·
          refine ⟨14882511823230694431052835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9921674548820462954035223 14882511823230694431052835)
          ·
            refine ⟨22323767734846041646579253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14882511823230694431052835 22323767734846041646579253)
            ·
              refine ⟨2092853225141816404366805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22323767734846041646579253 2092853225141816404366805)
              ·
                refine ⟨49051247464261321977347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2092853225141816404366805 49051247464261321977347)
                ·
                  rfl

theorem cell21_644807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 7].length) (baseStart_644807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644807 prefixEnd_644807 := by exact prefixLift 644807
  have htrace : WordTrace (prefixWord ++ tailWord_644807) baseStart_644807 baseEnd_644807 := by
    simpa [prefixWord, tailWord_644807, baseEnd_644807] using wordTrace_append hprefix tailTrace_644807
  have hstable : (prefixWord ++ tailWord_644807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644807).length < 2 ^ (prefixWord ++ tailWord_644807).sum := by decide
  have hdescent : baseEnd_644807 < baseStart_644807 := by decide
  rcases family_descends (prefixWord ++ tailWord_644807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644900 : List Nat := [2, 3, 1, 3, 2, 1, 3, 6]
def baseStart_644900 : Nat := 118140960795 + 644900 * 2 ^ 59
def prefixEnd_644900 : Nat := 4983230072969 + 3 ^ 40 * 644900 * 2
def baseEnd_644900 : Nat := 49058322086612156960617

theorem tailTrace_644900 : CollatzResearch.WordTrace tailWord_644900 prefixEnd_644900 49058322086612156960617 := by
  unfold tailWord_644900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11760717681822457498202077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15680956909096609997602769 11760717681822457498202077)
  ·
    refine ⟨4410269130683421561825779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11760717681822457498202077 4410269130683421561825779)
    ·
      refine ⟨6615403696025132342738669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4410269130683421561825779 6615403696025132342738669)
      ·
        refine ⟨2480776386009424628527001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6615403696025132342738669 2480776386009424628527001)
        ·
          refine ⟨1860582289507068471395251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2480776386009424628527001 1860582289507068471395251)
          ·
            refine ⟨2790873434260602707092877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860582289507068471395251 2790873434260602707092877)
            ·
              refine ⟨1046577537847726015159829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2790873434260602707092877 1046577537847726015159829)
              ·
                refine ⟨49058322086612156960617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1046577537847726015159829 49058322086612156960617)
                ·
                  rfl

theorem cell21_644900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_644900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644900 prefixEnd_644900 := by exact prefixLift 644900
  have htrace : WordTrace (prefixWord ++ tailWord_644900) baseStart_644900 baseEnd_644900 := by
    simpa [prefixWord, tailWord_644900, baseEnd_644900] using wordTrace_append hprefix tailTrace_644900
  have hstable : (prefixWord ++ tailWord_644900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644900).length < 2 ^ (prefixWord ++ tailWord_644900).sum := by decide
  have hdescent : baseEnd_644900 < baseStart_644900 := by decide
  rcases family_descends (prefixWord ++ tailWord_644900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644914 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_644914 : Nat := 118140960795 + 644914 * 2 ^ 59
def prefixEnd_644914 : Nat := 4983230072969 + 3 ^ 40 * 644914 * 2
def baseEnd_644914 : Nat := 147178161250575557648489

theorem tailTrace_644914 : CollatzResearch.WordTrace tailWord_644914 prefixEnd_644914 147178161250575557648489 := by
  unfold tailWord_644914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5880486496398548846853449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15681297323729463591609197 5880486496398548846853449)
  ·
    refine ⟨4410364872298911635140087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5880486496398548846853449 4410364872298911635140087)
    ·
      refine ⟨6615547308448367452710131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4410364872298911635140087 6615547308448367452710131)
      ·
        refine ⟨9923320962672551179065197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6615547308448367452710131 9923320962672551179065197)
        ·
          refine ⟨3721245361002206692149449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9923320962672551179065197 3721245361002206692149449)
          ·
            refine ⟨2790934020751655019112087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3721245361002206692149449 2790934020751655019112087)
            ·
              refine ⟨4186401031127482528668131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790934020751655019112087 4186401031127482528668131)
              ·
                refine ⟨6279601546691223793002197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4186401031127482528668131 6279601546691223793002197)
                ·
                  refine ⟨147178161250575557648489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6279601546691223793002197 147178161250575557648489)
                  ·
                    rfl

theorem cell21_644914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_644914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644914 prefixEnd_644914 := by exact prefixLift 644914
  have htrace : WordTrace (prefixWord ++ tailWord_644914) baseStart_644914 baseEnd_644914 := by
    simpa [prefixWord, tailWord_644914, baseEnd_644914] using wordTrace_append hprefix tailTrace_644914
  have hstable : (prefixWord ++ tailWord_644914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644914).length < 2 ^ (prefixWord ++ tailWord_644914).sum := by decide
  have hdescent : baseEnd_644914 < baseStart_644914 := by decide
  rcases family_descends (prefixWord ++ tailWord_644914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644917 : List Nat := [1, 3, 3, 1, 4, 1, 3, 5]
def baseStart_644917 : Nat := 118140960795 + 644917 * 2 ^ 59
def prefixEnd_644917 : Nat := 4983230072969 + 3 ^ 40 * 644917 * 2
def baseEnd_644917 : Nat := 49059615297149406366161

theorem tailTrace_644917 : CollatzResearch.WordTrace tailWord_644917 prefixEnd_644917 49059615297149406366161 := by
  unfold tailWord_644917
  simp only [CollatzResearch.WordTrace]
  refine ⟨23522055404583326899773005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15681370269722217933182003 23522055404583326899773005)
  ·
    refine ⟨8820770776718747587414877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23522055404583326899773005 8820770776718747587414877)
    ·
      refine ⟨3307789041269530345280579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8820770776718747587414877 3307789041269530345280579)
      ·
        refine ⟨4961683561904295517920869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3307789041269530345280579 4961683561904295517920869)
        ·
          refine ⟨930315667857055409610163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4961683561904295517920869 930315667857055409610163)
          ·
            refine ⟨1395473501785583114415245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930315667857055409610163 1395473501785583114415245)
            ·
              refine ⟨523302563169593667905717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1395473501785583114415245 523302563169593667905717)
              ·
                refine ⟨49059615297149406366161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 523302563169593667905717 49059615297149406366161)
                ·
                  rfl

theorem cell21_644917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 5].length) (baseStart_644917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644917 prefixEnd_644917 := by exact prefixLift 644917
  have htrace : WordTrace (prefixWord ++ tailWord_644917) baseStart_644917 baseEnd_644917 := by
    simpa [prefixWord, tailWord_644917, baseEnd_644917] using wordTrace_append hprefix tailTrace_644917
  have hstable : (prefixWord ++ tailWord_644917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644917).length < 2 ^ (prefixWord ++ tailWord_644917).sum := by decide
  have hdescent : baseEnd_644917 < baseStart_644917 := by decide
  rcases family_descends (prefixWord ++ tailWord_644917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644931 : List Nat := [1, 1, 1, 3, 1, 5, 1, 5, 3]
def baseStart_644931 : Nat := 118140960795 + 644931 * 2 ^ 59
def prefixEnd_644931 : Nat := 4983230072969 + 3 ^ 40 * 644931 * 2
def baseEnd_644931 : Nat := 147182040882187305865121

theorem tailTrace_644931 : CollatzResearch.WordTrace tailWord_644931 prefixEnd_644931 147182040882187305865121 := by
  unfold tailWord_644931
  simp only [CollatzResearch.WordTrace]
  refine ⟨23522566026532607290782647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15681710684355071527188431 23522566026532607290782647)
  ·
    refine ⟨35283849039798910936173971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23522566026532607290782647 35283849039798910936173971)
    ·
      refine ⟨52925773559698366404260957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35283849039798910936173971 52925773559698366404260957)
      ·
        refine ⟨19847165084886887401597859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52925773559698366404260957 19847165084886887401597859)
        ·
          refine ⟨29770747627330331102396789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19847165084886887401597859 29770747627330331102396789)
          ·
            refine ⟨2791007590062218540849699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29770747627330331102396789 2791007590062218540849699)
            ·
              refine ⟨4186511385093327811274549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2791007590062218540849699 4186511385093327811274549)
              ·
                refine ⟨392485442352499482306989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4186511385093327811274549 392485442352499482306989)
                ·
                  refine ⟨147182040882187305865121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392485442352499482306989 147182040882187305865121)
                  ·
                    rfl

theorem cell21_644931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 3].length) (baseStart_644931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644931 prefixEnd_644931 := by exact prefixLift 644931
  have htrace : WordTrace (prefixWord ++ tailWord_644931) baseStart_644931 baseEnd_644931 := by
    simpa [prefixWord, tailWord_644931, baseEnd_644931] using wordTrace_append hprefix tailTrace_644931
  have hstable : (prefixWord ++ tailWord_644931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644931).length < 2 ^ (prefixWord ++ tailWord_644931).sum := by decide
  have hdescent : baseEnd_644931 < baseStart_644931 := by decide
  rcases family_descends (prefixWord ++ tailWord_644931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644945 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 6]
def baseStart_644945 : Nat := 118140960795 + 644945 * 2 ^ 59
def prefixEnd_644945 : Nat := 4983230072969 + 3 ^ 40 * 644945 * 2
def baseEnd_644945 : Nat := 147185235872926392631759

theorem tailTrace_644945 : CollatzResearch.WordTrace tailWord_644945 prefixEnd_644945 147185235872926392631759 := by
  unfold tailWord_644945
  simp only [CollatzResearch.WordTrace]
  refine ⟨23523076648481887681792289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15682051098987925121194859 23523076648481887681792289)
  ·
    refine ⟨17642307486361415761344217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23523076648481887681792289 17642307486361415761344217)
    ·
      refine ⟨13231730614771061821008163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17642307486361415761344217 13231730614771061821008163)
      ·
        refine ⟨19847595922156592731512245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13231730614771061821008163 19847595922156592731512245)
        ·
          refine ⟨1860712117702180568579273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19847595922156592731512245 1860712117702180568579273)
          ·
            refine ⟨1395534088276635426434455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1860712117702180568579273 1395534088276635426434455)
            ·
              refine ⟨2093301132414953139651683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395534088276635426434455 2093301132414953139651683)
              ·
                refine ⟨3139951698622429709477525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2093301132414953139651683 3139951698622429709477525)
                ·
                  refine ⟨147185235872926392631759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3139951698622429709477525 147185235872926392631759)
                  ·
                    rfl

theorem cell21_644945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_644945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644945 prefixEnd_644945 := by exact prefixLift 644945
  have htrace : WordTrace (prefixWord ++ tailWord_644945) baseStart_644945 baseEnd_644945 := by
    simpa [prefixWord, tailWord_644945, baseEnd_644945] using wordTrace_append hprefix tailTrace_644945
  have hstable : (prefixWord ++ tailWord_644945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644945).length < 2 ^ (prefixWord ++ tailWord_644945).sum := by decide
  have hdescent : baseEnd_644945 < baseStart_644945 := by decide
  rcases family_descends (prefixWord ++ tailWord_644945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644948 : List Nat := [2, 4, 1, 1, 3, 1, 2, 4, 3]
def baseStart_644948 : Nat := 118140960795 + 644948 * 2 ^ 59
def prefixEnd_644948 : Nat := 4983230072969 + 3 ^ 40 * 644948 * 2
def baseEnd_644948 : Nat := 147185920513799054081753

theorem tailTrace_644948 : CollatzResearch.WordTrace tailWord_644948 prefixEnd_644948 147185920513799054081753 := by
  unfold tailWord_644948
  simp only [CollatzResearch.WordTrace]
  refine ⟨11761593033735509597075749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15682124044980679462767665 11761593033735509597075749)
  ·
    refine ⟨2205298693825408049451703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11761593033735509597075749 2205298693825408049451703)
    ·
      refine ⟨3307948040738112074177555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2205298693825408049451703 3307948040738112074177555)
      ·
        refine ⟨4961922061107168111266333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3307948040738112074177555 4961922061107168111266333)
        ·
          refine ⟨1860720772915188041724875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4961922061107168111266333 1860720772915188041724875)
          ·
            refine ⟨2791081159372782062587313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860720772915188041724875 2791081159372782062587313)
            ·
              refine ⟨2093310869529586546940485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2791081159372782062587313 2093310869529586546940485)
              ·
                refine ⟨392495788036797477551341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2093310869529586546940485 392495788036797477551341)
                ·
                  refine ⟨147185920513799054081753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392495788036797477551341 147185920513799054081753)
                  ·
                    rfl

theorem cell21_644948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_644948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644948 prefixEnd_644948 := by exact prefixLift 644948
  have htrace : WordTrace (prefixWord ++ tailWord_644948) baseStart_644948 baseEnd_644948 := by
    simpa [prefixWord, tailWord_644948, baseEnd_644948] using wordTrace_append hprefix tailTrace_644948
  have hstable : (prefixWord ++ tailWord_644948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644948).length < 2 ^ (prefixWord ++ tailWord_644948).sum := by decide
  have hdescent : baseEnd_644948 < baseStart_644948 := by decide
  rcases family_descends (prefixWord ++ tailWord_644948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644982 : List Nat := [5, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_644982 : Nat := 118140960795 + 644982 * 2 ^ 59
def prefixEnd_644982 : Nat := 4983230072969 + 3 ^ 40 * 644982 * 2
def baseEnd_644982 : Nat := 147193679777022550515017

theorem tailTrace_644982 : CollatzResearch.WordTrace tailWord_644982 prefixEnd_644982 147193679777022550515017 := by
  unfold tailWord_644982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470276634334240187555575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15682950766231895333926133 1470276634334240187555575)
  ·
    refine ⟨2205414951501360281333363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1470276634334240187555575 2205414951501360281333363)
    ·
      refine ⟨3308122427252040422000045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2205414951501360281333363 3308122427252040422000045)
      ·
        refine ⟨1240545910219515158250017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3308122427252040422000045 1240545910219515158250017)
        ·
          refine ⟨930409432664636368687513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1240545910219515158250017 930409432664636368687513)
          ·
            refine ⟨697807074498477276515635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930409432664636368687513 697807074498477276515635)
            ·
              refine ⟨1046710611747715914773453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697807074498477276515635 1046710611747715914773453)
              ·
                refine ⟨392516479405393468040045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1046710611747715914773453 392516479405393468040045)
                ·
                  refine ⟨147193679777022550515017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392516479405393468040045 147193679777022550515017)
                  ·
                    rfl

theorem cell21_644982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_644982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644982 prefixEnd_644982 := by exact prefixLift 644982
  have htrace : WordTrace (prefixWord ++ tailWord_644982) baseStart_644982 baseEnd_644982 := by
    simpa [prefixWord, tailWord_644982, baseEnd_644982] using wordTrace_append hprefix tailTrace_644982
  have hstable : (prefixWord ++ tailWord_644982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644982).length < 2 ^ (prefixWord ++ tailWord_644982).sum := by decide
  have hdescent : baseEnd_644982 < baseStart_644982 := by decide
  rcases family_descends (prefixWord ++ tailWord_644982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644993 : List Nat := [1, 2, 4, 4, 1, 2, 7]
def baseStart_644993 : Nat := 118140960795 + 644993 * 2 ^ 59
def prefixEnd_644993 : Nat := 4983230072969 + 3 ^ 40 * 644993 * 2
def baseEnd_644993 : Nat := 16355132236320997314629

theorem tailTrace_644993 : CollatzResearch.WordTrace tailWord_644993 prefixEnd_644993 16355132236320997314629 := by
  unfold tailWord_644993
  simp only [CollatzResearch.WordTrace]
  refine ⟨23524827352307991879539633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15683218234871994586359755 23524827352307991879539633)
  ·
    refine ⟨17643620514230993909654725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23524827352307991879539633 17643620514230993909654725)
    ·
      refine ⟨3308178846418311358060261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17643620514230993909654725 3308178846418311358060261)
      ·
        refine ⟨620283533703433379636299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3308178846418311358060261 620283533703433379636299)
        ·
          refine ⟨930425300555150069454449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620283533703433379636299 930425300555150069454449)
          ·
            refine ⟨697818975416362552090837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930425300555150069454449 697818975416362552090837)
            ·
              refine ⟨16355132236320997314629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 697818975416362552090837 16355132236320997314629)
              ·
                rfl

theorem cell21_644993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 7].length) (baseStart_644993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_644993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_644993 prefixEnd_644993 := by exact prefixLift 644993
  have htrace : WordTrace (prefixWord ++ tailWord_644993) baseStart_644993 baseEnd_644993 := by
    simpa [prefixWord, tailWord_644993, baseEnd_644993] using wordTrace_append hprefix tailTrace_644993
  have hstable : (prefixWord ++ tailWord_644993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644993).length < 2 ^ (prefixWord ++ tailWord_644993).sum := by decide
  have hdescent : baseEnd_644993 < baseStart_644993 := by decide
  rcases family_descends (prefixWord ++ tailWord_644993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645052 : List Nat := [2, 2, 2, 5, 1, 9]
def baseStart_645052 : Nat := 118140960795 + 645052 * 2 ^ 59
def prefixEnd_645052 : Nat := 4983230072969 + 3 ^ 40 * 645052 * 2
def baseEnd_645052 : Nat := 5452209434471036457341

theorem tailTrace_645052 : CollatzResearch.WordTrace tailWord_645052 prefixEnd_645052 5452209434471036457341 := by
  unfold tailWord_645052
  simp only [CollatzResearch.WordTrace]
  refine ⟨11763489629547122477968705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15684652839396163303958273 11763489629547122477968705)
  ·
    refine ⟨8822617222160341858476529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11763489629547122477968705 8822617222160341858476529)
    ·
      refine ⟨6616962916620256393857397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8822617222160341858476529 6616962916620256393857397)
      ·
        refine ⟨620340273433149036924131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6616962916620256393857397 620340273433149036924131)
        ·
          refine ⟨930510410149723555386197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620340273433149036924131 930510410149723555386197)
          ·
            refine ⟨5452209434471036457341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 930510410149723555386197 5452209434471036457341)
            ·
              rfl

theorem cell21_645052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 9].length) (baseStart_645052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_645052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_645052 prefixEnd_645052 := by exact prefixLift 645052
  have htrace : WordTrace (prefixWord ++ tailWord_645052) baseStart_645052 baseEnd_645052 := by
    simpa [prefixWord, tailWord_645052, baseEnd_645052] using wordTrace_append hprefix tailTrace_645052
  have hstable : (prefixWord ++ tailWord_645052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645052).length < 2 ^ (prefixWord ++ tailWord_645052).sum := by decide
  have hdescent : baseEnd_645052 < baseStart_645052 := by decide
  rcases family_descends (prefixWord ++ tailWord_645052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645176 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 5]
def baseStart_645176 : Nat := 118140960795 + 645176 * 2 ^ 59
def prefixEnd_645176 : Nat := 4983230072969 + 3 ^ 40 * 645176 * 2
def baseEnd_645176 : Nat := 147237953220121324281287

theorem tailTrace_645176 : CollatzResearch.WordTrace tailWord_645176 prefixEnd_645176 147237953220121324281287 := by
  unfold tailWord_645176
  simp only [CollatzResearch.WordTrace]
  refine ⟨11765750955322507066725691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15687667940430009422300921 11765750955322507066725691)
  ·
    refine ⟨17648626432983760600088537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11765750955322507066725691 17648626432983760600088537)
    ·
      refine ⟨13236469824737820450066403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17648626432983760600088537 13236469824737820450066403)
      ·
        refine ⟨19854704737106730675099605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13236469824737820450066403 19854704737106730675099605)
        ·
          refine ⟨465344642275939000197647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19854704737106730675099605 465344642275939000197647)
          ·
            refine ⟨698016963413908500296471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465344642275939000197647 698016963413908500296471)
            ·
              refine ⟨1047025445120862750444707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698016963413908500296471 1047025445120862750444707)
              ·
                refine ⟨1570538167681294125667061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047025445120862750444707 1570538167681294125667061)
                ·
                  refine ⟨147237953220121324281287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1570538167681294125667061 147237953220121324281287)
                  ·
                    rfl

theorem cell21_645176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 5].length) (baseStart_645176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_645176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_645176 prefixEnd_645176 := by exact prefixLift 645176
  have htrace : WordTrace (prefixWord ++ tailWord_645176) baseStart_645176 baseEnd_645176 := by
    simpa [prefixWord, tailWord_645176, baseEnd_645176] using wordTrace_append hprefix tailTrace_645176
  have hstable : (prefixWord ++ tailWord_645176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645176).length < 2 ^ (prefixWord ++ tailWord_645176).sum := by decide
  have hdescent : baseEnd_645176 < baseStart_645176 := by decide
  rcases family_descends (prefixWord ++ tailWord_645176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645201 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 7]
def baseStart_645201 : Nat := 118140960795 + 645201 * 2 ^ 59
def prefixEnd_645201 : Nat := 4983230072969 + 3 ^ 40 * 645201 * 2
def baseEnd_645201 : Nat := 147243658560726836364569

theorem tailTrace_645201 : CollatzResearch.WordTrace tailWord_645201 prefixEnd_645201 147243658560726836364569 := by
  unfold tailWord_645201
  simp only [CollatzResearch.WordTrace]
  refine ⟨23532413735554443403111457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15688275823702962268740971 23532413735554443403111457)
  ·
    refine ⟨17649310301665832552333593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23532413735554443403111457 17649310301665832552333593)
    ·
      refine ⟨13236982726249374414250195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17649310301665832552333593 13236982726249374414250195)
      ·
        refine ⟨19855474089374061621375293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13236982726249374414250195 19855474089374061621375293)
        ·
          refine ⟨7445802783515273108015735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19855474089374061621375293 7445802783515273108015735)
          ·
            refine ⟨11168704175272909662023603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7445802783515273108015735 11168704175272909662023603)
            ·
              refine ⟨16753056262909364493035405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11168704175272909662023603 16753056262909364493035405)
              ·
                refine ⟨6282396098591011684888277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16753056262909364493035405 6282396098591011684888277)
                ·
                  refine ⟨147243658560726836364569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6282396098591011684888277 147243658560726836364569)
                  ·
                    rfl

theorem cell21_645201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_645201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_645201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_645201 prefixEnd_645201 := by exact prefixLift 645201
  have htrace : WordTrace (prefixWord ++ tailWord_645201) baseStart_645201 baseEnd_645201 := by
    simpa [prefixWord, tailWord_645201, baseEnd_645201] using wordTrace_append hprefix tailTrace_645201
  have hstable : (prefixWord ++ tailWord_645201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645201).length < 2 ^ (prefixWord ++ tailWord_645201).sum := by decide
  have hdescent : baseEnd_645201 < baseStart_645201 := by decide
  rcases family_descends (prefixWord ++ tailWord_645201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645314 : List Nat := [3, 5, 1, 1, 1, 1, 4, 5]
def baseStart_645314 : Nat := 118140960795 + 645314 * 2 ^ 59
def prefixEnd_645314 : Nat := 4983230072969 + 3 ^ 40 * 645314 * 2
def baseEnd_645314 : Nat := 49089815566754583660335

theorem tailTrace_645314 : CollatzResearch.WordTrace tailWord_645314 prefixEnd_645314 49089815566754583660335 := by
  unfold tailWord_645314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5884133796036265925493749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15691023456096709134649997 5884133796036265925493749)
  ·
    refine ⟨551637543378399930515039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5884133796036265925493749 551637543378399930515039)
    ·
      refine ⟨827456315067599895772559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 551637543378399930515039 827456315067599895772559)
      ·
        refine ⟨1241184472601399843658839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827456315067599895772559 1241184472601399843658839)
        ·
          refine ⟨1861776708902099765488259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241184472601399843658839 1861776708902099765488259)
          ·
            refine ⟨2792665063353149648232389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861776708902099765488259 2792665063353149648232389)
            ·
              refine ⟨523624699378715559043573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2792665063353149648232389 523624699378715559043573)
              ·
                refine ⟨49089815566754583660335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 523624699378715559043573 49089815566754583660335)
                ·
                  rfl

theorem cell21_645314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_645314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_645314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_645314 prefixEnd_645314 := by exact prefixLift 645314
  have htrace : WordTrace (prefixWord ++ tailWord_645314) baseStart_645314 baseEnd_645314 := by
    simpa [prefixWord, tailWord_645314, baseEnd_645314] using wordTrace_append hprefix tailTrace_645314
  have hstable : (prefixWord ++ tailWord_645314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645314).length < 2 ^ (prefixWord ++ tailWord_645314).sum := by decide
  have hdescent : baseEnd_645314 < baseStart_645314 := by decide
  rcases family_descends (prefixWord ++ tailWord_645314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645646 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_645646 : Nat := 118140960795 + 645646 * 2 ^ 59
def prefixEnd_645646 : Nat := 4983230072969 + 3 ^ 40 * 645646 * 2
def baseEnd_645646 : Nat := 147345213623504951446993

theorem tailTrace_645646 : CollatzResearch.WordTrace tailWord_645646 prefixEnd_645646 147345213623504951446993 := by
  unfold tailWord_645646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2943580527367785550382599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15699096145961522935373861 2943580527367785550382599)
  ·
    refine ⟨4415370791051678325573899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2943580527367785550382599 4415370791051678325573899)
    ·
      refine ⟨6623056186577517488360849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4415370791051678325573899 6623056186577517488360849)
      ·
        refine ⟨4967292139933138116270637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6623056186577517488360849 4967292139933138116270637)
        ·
          refine ⟨1862734552474926793601489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4967292139933138116270637 1862734552474926793601489)
          ·
            refine ⟨1397050914356195095201117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1862734552474926793601489 1397050914356195095201117)
            ·
              refine ⟨523894092883573160700419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1397050914356195095201117 523894092883573160700419)
              ·
                refine ⟨785841139325359741050629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523894092883573160700419 785841139325359741050629)
                ·
                  refine ⟨147345213623504951446993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 785841139325359741050629 147345213623504951446993)
                  ·
                    rfl

theorem cell21_645646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_645646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_645646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_645646 prefixEnd_645646 := by exact prefixLift 645646
  have htrace : WordTrace (prefixWord ++ tailWord_645646) baseStart_645646 baseEnd_645646 := by
    simpa [prefixWord, tailWord_645646, baseEnd_645646] using wordTrace_append hprefix tailTrace_645646
  have hstable : (prefixWord ++ tailWord_645646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645646).length < 2 ^ (prefixWord ++ tailWord_645646).sum := by decide
  have hdescent : baseEnd_645646 < baseStart_645646 := by decide
  rcases family_descends (prefixWord ++ tailWord_645646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645660 : List Nat := [2, 2, 3, 1, 2, 4, 2, 5]
def baseStart_645660 : Nat := 118140960795 + 645660 * 2 ^ 59
def prefixEnd_645660 : Nat := 4983230072969 + 3 ^ 40 * 645660 * 2
def baseEnd_645660 : Nat := 49116136204748012737877

theorem tailTrace_645660 : CollatzResearch.WordTrace tailWord_645660 prefixEnd_645660 49116136204748012737877 := by
  unfold tailWord_645660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11774577420445782397035217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15699436560594376529380289 11774577420445782397035217)
  ·
    refine ⟨8830933065334336797776413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11774577420445782397035217 8830933065334336797776413)
    ·
      refine ⟨3311599899500376299166155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8830933065334336797776413 3311599899500376299166155)
      ·
        refine ⟨4967399849250564448749233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3311599899500376299166155 4967399849250564448749233)
        ·
          refine ⟨3725549886937923336561925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4967399849250564448749233 3725549886937923336561925)
          ·
            refine ⟨698540603800860625605361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3725549886937923336561925 698540603800860625605361)
            ·
              refine ⟨523905452850645469204021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698540603800860625605361 523905452850645469204021)
              ·
                refine ⟨49116136204748012737877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 523905452850645469204021 49116136204748012737877)
                ·
                  rfl

theorem cell21_645660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_645660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_645660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_645660 prefixEnd_645660 := by exact prefixLift 645660
  have htrace : WordTrace (prefixWord ++ tailWord_645660) baseStart_645660 baseEnd_645660 := by
    simpa [prefixWord, tailWord_645660, baseEnd_645660] using wordTrace_append hprefix tailTrace_645660
  have hstable : (prefixWord ++ tailWord_645660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645660).length < 2 ^ (prefixWord ++ tailWord_645660).sum := by decide
  have hdescent : baseEnd_645660 < baseStart_645660 := by decide
  rcases family_descends (prefixWord ++ tailWord_645660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645688 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 4]
def baseStart_645688 : Nat := 118140960795 + 645688 * 2 ^ 59
def prefixEnd_645688 : Nat := 4983230072969 + 3 ^ 40 * 645688 * 2
def baseEnd_645688 : Nat := 147354798595722211746907

theorem tailTrace_645688 : CollatzResearch.WordTrace tailWord_645688 prefixEnd_645688 147354798595722211746907 := by
  unfold tailWord_645688
  simp only [CollatzResearch.WordTrace]
  refine ⟨11775088042395062788044859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15700117389860083717393145 11775088042395062788044859)
  ·
    refine ⟨17662632063592594182067289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11775088042395062788044859 17662632063592594182067289)
    ·
      refine ⟨13246974047694445636550467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17662632063592594182067289 13246974047694445636550467)
      ·
        refine ⟨19870461071541668454825701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13246974047694445636550467 19870461071541668454825701)
        ·
          refine ⟨3725711450914062835279819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19870461071541668454825701 3725711450914062835279819)
          ·
            refine ⟨5588567176371094252919729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3725711450914062835279819 5588567176371094252919729)
            ·
              refine ⟨4191425382278320689689797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5588567176371094252919729 4191425382278320689689797)
              ·
                refine ⟨785892259177185129316837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4191425382278320689689797 785892259177185129316837)
                ·
                  refine ⟨147354798595722211746907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 785892259177185129316837 147354798595722211746907)
                  ·
                    rfl

theorem cell21_645688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_645688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_645688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_645688 prefixEnd_645688 := by exact prefixLift 645688
  have htrace : WordTrace (prefixWord ++ tailWord_645688) baseStart_645688 baseEnd_645688 := by
    simpa [prefixWord, tailWord_645688, baseEnd_645688] using wordTrace_append hprefix tailTrace_645688
  have hstable : (prefixWord ++ tailWord_645688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645688).length < 2 ^ (prefixWord ++ tailWord_645688).sum := by decide
  have hdescent : baseEnd_645688 < baseStart_645688 := by decide
  rcases family_descends (prefixWord ++ tailWord_645688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645874 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_645874 : Nat := 118140960795 + 645874 * 2 ^ 59
def prefixEnd_645874 : Nat := 4983230072969 + 3 ^ 40 * 645874 * 2
def baseEnd_645874 : Nat := 147397246329827221646527

theorem tailTrace_645874 : CollatzResearch.WordTrace tailWord_645874 prefixEnd_645874 147397246329827221646527 := by
  unfold tailWord_645874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5889240015529069835590169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15704640041410852894907117 5889240015529069835590169)
  ·
    refine ⟨4416930011646802376692627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5889240015529069835590169 4416930011646802376692627)
    ·
      refine ⟨6625395017470203565038941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4416930011646802376692627 6625395017470203565038941)
      ·
        refine ⟨2484523131551326336889603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6625395017470203565038941 2484523131551326336889603)
        ·
          refine ⟨3726784697326989505334405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484523131551326336889603 3726784697326989505334405)
          ·
            refine ⟨698772130748810532250201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3726784697326989505334405 698772130748810532250201)
            ·
              refine ⟨524079098061607899187651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698772130748810532250201 524079098061607899187651)
              ·
                refine ⟨786118647092411848781477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524079098061607899187651 786118647092411848781477)
                ·
                  refine ⟨147397246329827221646527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 786118647092411848781477 147397246329827221646527)
                  ·
                    rfl

theorem cell21_645874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_645874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_645874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_645874 prefixEnd_645874 := by exact prefixLift 645874
  have htrace : WordTrace (prefixWord ++ tailWord_645874) baseStart_645874 baseEnd_645874 := by
    simpa [prefixWord, tailWord_645874, baseEnd_645874] using wordTrace_append hprefix tailTrace_645874
  have hstable : (prefixWord ++ tailWord_645874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645874).length < 2 ^ (prefixWord ++ tailWord_645874).sum := by decide
  have hdescent : baseEnd_645874 < baseStart_645874 := by decide
  rcases family_descends (prefixWord ++ tailWord_645874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645902 : List Nat := [4, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_645902 : Nat := 118140960795 + 645902 * 2 ^ 59
def prefixEnd_645902 : Nat := 4983230072969 + 3 ^ 40 * 645902 * 2
def baseEnd_645902 : Nat := 147403636311305395179803

theorem tailTrace_645902 : CollatzResearch.WordTrace tailWord_645902 prefixEnd_645902 147403636311305395179803 := by
  unfold tailWord_645902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2944747663251855015547495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15705320870676560082919973 2944747663251855015547495)
  ·
    refine ⟨4417121494877782523321243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2944747663251855015547495 4417121494877782523321243)
    ·
      refine ⟨6625682242316673784981865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4417121494877782523321243 6625682242316673784981865)
      ·
        refine ⟨4969261681737505338736399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6625682242316673784981865 4969261681737505338736399)
        ·
          refine ⟨7453892522606258008104599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969261681737505338736399 7453892522606258008104599)
          ·
            refine ⟨11180838783909387012156899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7453892522606258008104599 11180838783909387012156899)
            ·
              refine ⟨16771258175864080518235349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11180838783909387012156899 16771258175864080518235349)
              ·
                refine ⟨393076363496814387146141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16771258175864080518235349 393076363496814387146141)
                ·
                  refine ⟨147403636311305395179803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393076363496814387146141 147403636311305395179803)
                  ·
                    rfl

theorem cell21_645902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_645902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_645902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_645902 prefixEnd_645902 := by exact prefixLift 645902
  have htrace : WordTrace (prefixWord ++ tailWord_645902) baseStart_645902 baseEnd_645902 := by
    simpa [prefixWord, tailWord_645902, baseEnd_645902] using wordTrace_append hprefix tailTrace_645902
  have hstable : (prefixWord ++ tailWord_645902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645902).length < 2 ^ (prefixWord ++ tailWord_645902).sum := by decide
  have hdescent : baseEnd_645902 < baseStart_645902 := by decide
  rcases family_descends (prefixWord ++ tailWord_645902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645916 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 4]
def baseStart_645916 : Nat := 118140960795 + 645916 * 2 ^ 59
def prefixEnd_645916 : Nat := 4983230072969 + 3 ^ 40 * 645916 * 2
def baseEnd_645916 : Nat := 147406831302044481946441

theorem tailTrace_645916 : CollatzResearch.WordTrace tailWord_645916 prefixEnd_645916 147406831302044481946441 := by
  unfold tailWord_645916
  simp only [CollatzResearch.WordTrace]
  refine ⟨11779245963982060257694801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15705661285309413676926401 11779245963982060257694801)
  ·
    refine ⟨8834434472986545193271101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11779245963982060257694801 8834434472986545193271101)
    ·
      refine ⟨3312912927369954447476663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8834434472986545193271101 3312912927369954447476663)
      ·
        refine ⟨4969369391054931671214995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3312912927369954447476663 4969369391054931671214995)
        ·
          refine ⟨7454054086582397506822493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969369391054931671214995 7454054086582397506822493)
          ·
            refine ⟨2795270282468399065058435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7454054086582397506822493 2795270282468399065058435)
            ·
              refine ⟨4192905423702598597587653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2795270282468399065058435 4192905423702598597587653)
              ·
                refine ⟨786169766944237237047685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4192905423702598597587653 786169766944237237047685)
                ·
                  refine ⟨147406831302044481946441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 786169766944237237047685 147406831302044481946441)
                  ·
                    rfl

theorem cell21_645916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_645916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_645916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_645916 prefixEnd_645916 := by exact prefixLift 645916
  have htrace : WordTrace (prefixWord ++ tailWord_645916) baseStart_645916 baseEnd_645916 := by
    simpa [prefixWord, tailWord_645916, baseEnd_645916] using wordTrace_append hprefix tailTrace_645916
  have hstable : (prefixWord ++ tailWord_645916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645916).length < 2 ^ (prefixWord ++ tailWord_645916).sum := by decide
  have hdescent : baseEnd_645916 < baseStart_645916 := by decide
  rcases family_descends (prefixWord ++ tailWord_645916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645919 : List Nat := [1, 1, 2, 4, 2, 2, 4, 2, 3]
def baseStart_645919 : Nat := 118140960795 + 645919 * 2 ^ 59
def prefixEnd_645919 : Nat := 4983230072969 + 3 ^ 40 * 645919 * 2
def baseEnd_645919 : Nat := 147407515942917143396435

theorem tailTrace_645919 : CollatzResearch.WordTrace tailWord_645919 prefixEnd_645919 147407515942917143396435 := by
  unfold tailWord_645919
  simp only [CollatzResearch.WordTrace]
  refine ⟨23558601346953252027748811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15705734231302168018499207 23558601346953252027748811)
  ·
    refine ⟨35337902020429878041623217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23558601346953252027748811 35337902020429878041623217)
    ·
      refine ⟨26503426515322408531217413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35337902020429878041623217 26503426515322408531217413)
      ·
        refine ⟨4969392471622951599603265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26503426515322408531217413 4969392471622951599603265)
        ·
          refine ⟨3727044353717213699702449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4969392471622951599603265 3727044353717213699702449)
          ·
            refine ⟨2795283265287910274776837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3727044353717213699702449 2795283265287910274776837)
            ·
              refine ⟨524115612241483176520657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2795283265287910274776837 524115612241483176520657)
              ·
                refine ⟨393086709181112382390493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524115612241483176520657 393086709181112382390493)
                ·
                  refine ⟨147407515942917143396435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393086709181112382390493 147407515942917143396435)
                  ·
                    rfl

theorem cell21_645919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 3].length) (baseStart_645919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_645919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_645919 prefixEnd_645919 := by exact prefixLift 645919
  have htrace : WordTrace (prefixWord ++ tailWord_645919) baseStart_645919 baseEnd_645919 := by
    simpa [prefixWord, tailWord_645919, baseEnd_645919] using wordTrace_append hprefix tailTrace_645919
  have hstable : (prefixWord ++ tailWord_645919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645919).length < 2 ^ (prefixWord ++ tailWord_645919).sum := by decide
  have hdescent : baseEnd_645919 < baseStart_645919 := by decide
  rcases family_descends (prefixWord ++ tailWord_645919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_645978 : List Nat := [3, 1, 1, 2, 1, 4, 2, 4, 3]
def baseStart_645978 : Nat := 118140960795 + 645978 * 2 ^ 59
def prefixEnd_645978 : Nat := 4983230072969 + 3 ^ 40 * 645978 * 2
def baseEnd_645978 : Nat := 147420980546746151912981

theorem tailTrace_645978 : CollatzResearch.WordTrace tailWord_645978 prefixEnd_645978 147420980546746151912981 := by
  unfold tailWord_645978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5890188313434876276036647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15707168835826336736097725 5890188313434876276036647)
  ·
    refine ⟨8835282470152314414054971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5890188313434876276036647 8835282470152314414054971)
    ·
      refine ⟨13252923705228471621082457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8835282470152314414054971 13252923705228471621082457)
      ·
        refine ⟨9939692778921353715811843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13252923705228471621082457 9939692778921353715811843)
        ·
          refine ⟨14909539168382030573717765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9939692778921353715811843 14909539168382030573717765)
          ·
            refine ⟨2795538594071630732572081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14909539168382030573717765 2795538594071630732572081)
            ·
              refine ⟨2096653945553723049429061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2795538594071630732572081 2096653945553723049429061)
              ·
                refine ⟨393122614791323071767949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2096653945553723049429061 393122614791323071767949)
                ·
                  refine ⟨147420980546746151912981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393122614791323071767949 147420980546746151912981)
                  ·
                    rfl

theorem cell21_645978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_645978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_645978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_645978 prefixEnd_645978 := by exact prefixLift 645978
  have htrace : WordTrace (prefixWord ++ tailWord_645978) baseStart_645978 baseEnd_645978 := by
    simpa [prefixWord, tailWord_645978, baseEnd_645978] using wordTrace_append hprefix tailTrace_645978
  have hstable : (prefixWord ++ tailWord_645978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_645978).length < 2 ^ (prefixWord ++ tailWord_645978).sum := by decide
  have hdescent : baseEnd_645978 < baseStart_645978 := by decide
  rcases family_descends (prefixWord ++ tailWord_645978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646037 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 5]
def baseStart_646037 : Nat := 118140960795 + 646037 * 2 ^ 59
def prefixEnd_646037 : Nat := 4983230072969 + 3 ^ 40 * 646037 * 2
def baseEnd_646037 : Nat := 147434445150575160429527

theorem tailTrace_646037 : CollatzResearch.WordTrace tailWord_646037 prefixEnd_646037 147434445150575160429527 := by
  unfold tailWord_646037
  simp only [CollatzResearch.WordTrace]
  refine ⟨23562905160525758180544365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15708603440350505453696243 23562905160525758180544365)
  ·
    refine ⟨8836089435197159317704137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23562905160525758180544365 8836089435197159317704137)
    ·
      refine ⟨6627067076397869488278103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8836089435197159317704137 6627067076397869488278103)
      ·
        refine ⟨9940600614596804232417155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6627067076397869488278103 9940600614596804232417155)
        ·
          refine ⟨14910900921895206348625733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9940600614596804232417155 14910900921895206348625733)
          ·
            refine ⟨2795793922855351190367325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14910900921895206348625733 2795793922855351190367325)
            ·
              refine ⟨1048422721070756696387747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2795793922855351190367325 1048422721070756696387747)
              ·
                refine ⟨1572634081606135044581621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048422721070756696387747 1572634081606135044581621)
                ·
                  refine ⟨147434445150575160429527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1572634081606135044581621 147434445150575160429527)
                  ·
                    rfl

theorem cell21_646037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_646037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646037 prefixEnd_646037 := by exact prefixLift 646037
  have htrace : WordTrace (prefixWord ++ tailWord_646037) baseStart_646037 baseEnd_646037 := by
    simpa [prefixWord, tailWord_646037, baseEnd_646037] using wordTrace_append hprefix tailTrace_646037
  have hstable : (prefixWord ++ tailWord_646037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646037).length < 2 ^ (prefixWord ++ tailWord_646037).sum := by decide
  have hdescent : baseEnd_646037 < baseStart_646037 := by decide
  rcases family_descends (prefixWord ++ tailWord_646037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646082 : List Nat := [3, 5, 13]
def baseStart_646082 : Nat := 118140960795 + 646082 * 2 ^ 59
def prefixEnd_646082 : Nat := 4983230072969 + 3 ^ 40 * 646082 * 2
def baseEnd_646082 : Nat := 202256124504341676515

theorem tailTrace_646082 : CollatzResearch.WordTrace tailWord_646082 prefixEnd_646082 202256124504341676515 := by
  unfold tailWord_646082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5891136611340682716483125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15709697630241820577288333 5891136611340682716483125)
  ·
    refine ⟨552294057313189004670293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5891136611340682716483125 552294057313189004670293)
    ·
      refine ⟨202256124504341676515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 552294057313189004670293 202256124504341676515)
      ·
        rfl

theorem cell21_646082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 13].length) (baseStart_646082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646082 prefixEnd_646082 := by exact prefixLift 646082
  have htrace : WordTrace (prefixWord ++ tailWord_646082) baseStart_646082 baseEnd_646082 := by
    simpa [prefixWord, tailWord_646082, baseEnd_646082] using wordTrace_append hprefix tailTrace_646082
  have hstable : (prefixWord ++ tailWord_646082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646082).length < 2 ^ (prefixWord ++ tailWord_646082).sum := by decide
  have hdescent : baseEnd_646082 < baseStart_646082 := by decide
  rcases family_descends (prefixWord ++ tailWord_646082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646088 : List Nat := [2, 1, 3, 1, 5, 2, 2, 2, 3]
def baseStart_646088 : Nat := 118140960795 + 646088 * 2 ^ 59
def prefixEnd_646088 : Nat := 4983230072969 + 3 ^ 40 * 646088 * 2
def baseEnd_646088 : Nat := 147446084045410405079423

theorem tailTrace_646088 : CollatzResearch.WordTrace tailWord_646088 prefixEnd_646088 147446084045410405079423 := by
  unfold tailWord_646088
  simp only [CollatzResearch.WordTrace]
  refine ⟨11782382641670496945325459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15709843522227329260433945 11782382641670496945325459)
  ·
    refine ⟨17673573962505745417988189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11782382641670496945325459 17673573962505745417988189)
    ·
      refine ⟨6627590235939654531745571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17673573962505745417988189 6627590235939654531745571)
      ·
        refine ⟨9941385353909481797618357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6627590235939654531745571 9941385353909481797618357)
        ·
          refine ⟨932004876929013918526721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9941385353909481797618357 932004876929013918526721)
          ·
            refine ⟨699003657696760438895041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 932004876929013918526721 699003657696760438895041)
            ·
              refine ⟨524252743272570329171281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699003657696760438895041 524252743272570329171281)
              ·
                refine ⟨393189557454427746878461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524252743272570329171281 393189557454427746878461)
                ·
                  refine ⟨147446084045410405079423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393189557454427746878461 147446084045410405079423)
                  ·
                    rfl

theorem cell21_646088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 3].length) (baseStart_646088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646088 prefixEnd_646088 := by exact prefixLift 646088
  have htrace : WordTrace (prefixWord ++ tailWord_646088) baseStart_646088 baseEnd_646088 := by
    simpa [prefixWord, tailWord_646088, baseEnd_646088] using wordTrace_append hprefix tailTrace_646088
  have hstable : (prefixWord ++ tailWord_646088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646088).length < 2 ^ (prefixWord ++ tailWord_646088).sum := by decide
  have hdescent : baseEnd_646088 < baseStart_646088 := by decide
  rcases family_descends (prefixWord ++ tailWord_646088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646096 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_646096 : Nat := 118140960795 + 646096 * 2 ^ 59
def prefixEnd_646096 : Nat := 4983230072969 + 3 ^ 40 * 646096 * 2
def baseEnd_646096 : Nat := 147447909754404168946073

theorem tailTrace_646096 : CollatzResearch.WordTrace tailWord_646096 prefixEnd_646096 147447909754404168946073 := by
  unfold tailWord_646096
  simp only [CollatzResearch.WordTrace]
  refine ⟨11782528533656005628471071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15710038044874674171294761 11782528533656005628471071)
  ·
    refine ⟨17673792800484008442706607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11782528533656005628471071 17673792800484008442706607)
    ·
      refine ⟨26510689200726012664059911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17673792800484008442706607 26510689200726012664059911)
      ·
        refine ⟨39766033801089018996089867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26510689200726012664059911 39766033801089018996089867)
        ·
          refine ⟨59649050701633528494134801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39766033801089018996089867 59649050701633528494134801)
          ·
            refine ⟨44736788026225146370601101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59649050701633528494134801 44736788026225146370601101)
            ·
              refine ⟨16776295509834429888975413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44736788026225146370601101 16776295509834429888975413)
              ·
                refine ⟨1572777704046977802091445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16776295509834429888975413 1572777704046977802091445)
                ·
                  refine ⟨147447909754404168946073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1572777704046977802091445 147447909754404168946073)
                  ·
                    rfl

theorem cell21_646096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_646096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646096 prefixEnd_646096 := by exact prefixLift 646096
  have htrace : WordTrace (prefixWord ++ tailWord_646096) baseStart_646096 baseEnd_646096 := by
    simpa [prefixWord, tailWord_646096, baseEnd_646096] using wordTrace_append hprefix tailTrace_646096
  have hstable : (prefixWord ++ tailWord_646096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646096).length < 2 ^ (prefixWord ++ tailWord_646096).sum := by decide
  have hdescent : baseEnd_646096 < baseStart_646096 := by decide
  rcases family_descends (prefixWord ++ tailWord_646096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646175 : List Nat := [1, 1, 2, 4, 1, 5, 2, 5]
def baseStart_646175 : Nat := 118140960795 + 646175 * 2 ^ 59
def prefixEnd_646175 : Nat := 4983230072969 + 3 ^ 40 * 646175 * 2
def baseEnd_646175 : Nat := 49155312876905862376415

theorem tailTrace_646175 : CollatzResearch.WordTrace tailWord_646175 prefixEnd_646175 49155312876905862376415 := by
  unfold tailWord_646175
  simp only [CollatzResearch.WordTrace]
  refine ⟨23567938434025807749067979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15711958956017205166045319 23567938434025807749067979)
  ·
    refine ⟨35351907651038711623601969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23567938434025807749067979 35351907651038711623601969)
    ·
      refine ⟨26513930738279033717701477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35351907651038711623601969 26513930738279033717701477)
      ·
        refine ⟨4971362013427318822069027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26513930738279033717701477 4971362013427318822069027)
        ·
          refine ⟨7457043020140978233103541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4971362013427318822069027 7457043020140978233103541)
          ·
            refine ⟨699097783138216709353457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7457043020140978233103541 699097783138216709353457)
            ·
              refine ⟨524323337353662532015093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699097783138216709353457 524323337353662532015093)
              ·
                refine ⟨49155312876905862376415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 524323337353662532015093 49155312876905862376415)
                ·
                  rfl

theorem cell21_646175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 5].length) (baseStart_646175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646175 prefixEnd_646175 := by exact prefixLift 646175
  have htrace : WordTrace (prefixWord ++ tailWord_646175) baseStart_646175 baseEnd_646175 := by
    simpa [prefixWord, tailWord_646175, baseEnd_646175] using wordTrace_append hprefix tailTrace_646175
  have hstable : (prefixWord ++ tailWord_646175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646175).length < 2 ^ (prefixWord ++ tailWord_646175).sum := by decide
  have hdescent : baseEnd_646175 < baseStart_646175 := by decide
  rcases family_descends (prefixWord ++ tailWord_646175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646206 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_646206 : Nat := 118140960795 + 646206 * 2 ^ 59
def prefixEnd_646206 : Nat := 4983230072969 + 3 ^ 40 * 646206 * 2
def baseEnd_646206 : Nat := 147473013253068422112515

theorem tailTrace_646206 : CollatzResearch.WordTrace tailWord_646206 prefixEnd_646206 147473013253068422112515 := by
  unfold tailWord_646206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2946133637114187505430809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15712712731275666695630981 2946133637114187505430809)
  ·
    refine ⟨2209600227835640629073107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2946133637114187505430809 2209600227835640629073107)
    ·
      refine ⟨3314400341753460943609661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2209600227835640629073107 3314400341753460943609661)
      ·
        refine ⟨1242900128157547853853623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3314400341753460943609661 1242900128157547853853623)
        ·
          refine ⟨1864350192236321780780435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242900128157547853853623 1864350192236321780780435)
          ·
            refine ⟨2796525288354482671170653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864350192236321780780435 2796525288354482671170653)
            ·
              refine ⟨1048696983132931001688995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2796525288354482671170653 1048696983132931001688995)
              ·
                refine ⟨1573045474699396502533493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048696983132931001688995 1573045474699396502533493)
                ·
                  refine ⟨147473013253068422112515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1573045474699396502533493 147473013253068422112515)
                  ·
                    rfl

theorem cell21_646206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_646206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646206 prefixEnd_646206 := by exact prefixLift 646206
  have htrace : WordTrace (prefixWord ++ tailWord_646206) baseStart_646206 baseEnd_646206 := by
    simpa [prefixWord, tailWord_646206, baseEnd_646206] using wordTrace_append hprefix tailTrace_646206
  have hstable : (prefixWord ++ tailWord_646206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646206).length < 2 ^ (prefixWord ++ tailWord_646206).sum := by decide
  have hdescent : baseEnd_646206 < baseStart_646206 := by decide
  rcases family_descends (prefixWord ++ tailWord_646206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646369 : List Nat := [1, 2, 3, 1, 3, 2, 9]
def baseStart_646369 : Nat := 118140960795 + 646369 * 2 ^ 59
def prefixEnd_646369 : Nat := 4983230072969 + 3 ^ 40 * 646369 * 2
def baseEnd_646369 : Nat := 16390023563757373432835

theorem tailTrace_646369 : CollatzResearch.WordTrace tailWord_646369 prefixEnd_646369 16390023563757373432835 := by
  unfold tailWord_646369
  simp only [CollatzResearch.WordTrace]
  refine ⟨23575014195322978881630161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15716676130215319254420107 23575014195322978881630161)
  ·
    refine ⟨17681260646492234161222621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23575014195322978881630161 17681260646492234161222621)
    ·
      refine ⟨6630472742434587810458483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17681260646492234161222621 6630472742434587810458483)
      ·
        refine ⟨9945709113651881715687725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6630472742434587810458483 9945709113651881715687725)
        ·
          refine ⟨3729640917619455643382897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9945709113651881715687725 3729640917619455643382897)
          ·
            refine ⟨2797230688214591732537173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3729640917619455643382897 2797230688214591732537173)
            ·
              refine ⟨16390023563757373432835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2797230688214591732537173 16390023563757373432835)
              ·
                rfl

theorem cell21_646369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 9].length) (baseStart_646369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646369 prefixEnd_646369 := by exact prefixLift 646369
  have htrace : WordTrace (prefixWord ++ tailWord_646369) baseStart_646369 baseEnd_646369 := by
    simpa [prefixWord, tailWord_646369, baseEnd_646369] using wordTrace_append hprefix tailTrace_646369
  have hstable : (prefixWord ++ tailWord_646369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646369).length < 2 ^ (prefixWord ++ tailWord_646369).sum := by decide
  have hdescent : baseEnd_646369 < baseStart_646369 := by decide
  rcases family_descends (prefixWord ++ tailWord_646369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646375 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 5]
def baseStart_646375 : Nat := 118140960795 + 646375 * 2 ^ 59
def prefixEnd_646375 : Nat := 4983230072969 + 3 ^ 40 * 646375 * 2
def baseEnd_646375 : Nat := 147511581355561683795503

theorem tailTrace_646375 : CollatzResearch.WordTrace tailWord_646375 prefixEnd_646375 147511581355561683795503 := by
  unfold tailWord_646375
  simp only [CollatzResearch.WordTrace]
  refine ⟨23575233033301241906348579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15716822022200827937565719 23575233033301241906348579)
  ·
    refine ⟨35362849549951862859522869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23575233033301241906348579 35362849549951862859522869)
    ·
      refine ⟨3315267145307987143080269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35362849549951862859522869 3315267145307987143080269)
      ·
        refine ⟨1243225179490495178655101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3315267145307987143080269 1243225179490495178655101)
        ·
          refine ⟨466209442308935691995663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1243225179490495178655101 466209442308935691995663)
          ·
            refine ⟨699314163463403537993495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466209442308935691995663 699314163463403537993495)
            ·
              refine ⟨1048971245195105306990243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699314163463403537993495 1048971245195105306990243)
              ·
                refine ⟨1573456867792657960485365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048971245195105306990243 1573456867792657960485365)
                ·
                  refine ⟨147511581355561683795503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1573456867792657960485365 147511581355561683795503)
                  ·
                    rfl

theorem cell21_646375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 5].length) (baseStart_646375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646375 prefixEnd_646375 := by exact prefixLift 646375
  have htrace : WordTrace (prefixWord ++ tailWord_646375) baseStart_646375 baseEnd_646375 := by
    simpa [prefixWord, tailWord_646375, baseEnd_646375] using wordTrace_append hprefix tailTrace_646375
  have hstable : (prefixWord ++ tailWord_646375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646375).length < 2 ^ (prefixWord ++ tailWord_646375).sum := by decide
  have hdescent : baseEnd_646375 < baseStart_646375 := by decide
  rcases family_descends (prefixWord ++ tailWord_646375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646417 : List Nat := [1, 2, 2, 1, 1, 4, 2, 5, 3]
def baseStart_646417 : Nat := 118140960795 + 646417 * 2 ^ 59
def prefixEnd_646417 : Nat := 4983230072969 + 3 ^ 40 * 646417 * 2
def baseEnd_646417 : Nat := 147521166327778944095417

theorem tailTrace_646417 : CollatzResearch.WordTrace tailWord_646417 prefixEnd_646417 147521166327778944095417 := by
  unfold tailWord_646417
  simp only [CollatzResearch.WordTrace]
  refine ⟨23576764899149083079377505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15717843266099388719585003 23576764899149083079377505)
  ·
    refine ⟨17682573674361812309533129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23576764899149083079377505 17682573674361812309533129)
    ·
      refine ⟨13261930255771359232149847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17682573674361812309533129 13261930255771359232149847)
      ·
        refine ⟨19892895383657038848224771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13261930255771359232149847 19892895383657038848224771)
        ·
          refine ⟨29839343075485558272337157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19892895383657038848224771 29839343075485558272337157)
          ·
            refine ⟨5594876826653542176063217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29839343075485558272337157 5594876826653542176063217)
            ·
              refine ⟨4196157619990156632047413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5594876826653542176063217 4196157619990156632047413)
              ·
                refine ⟨393389776874077184254445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4196157619990156632047413 393389776874077184254445)
                ·
                  refine ⟨147521166327778944095417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393389776874077184254445 147521166327778944095417)
                  ·
                    rfl

theorem cell21_646417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 3].length) (baseStart_646417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646417 prefixEnd_646417 := by exact prefixLift 646417
  have htrace : WordTrace (prefixWord ++ tailWord_646417) baseStart_646417 baseEnd_646417 := by
    simpa [prefixWord, tailWord_646417, baseEnd_646417] using wordTrace_append hprefix tailTrace_646417
  have hstable : (prefixWord ++ tailWord_646417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646417).length < 2 ^ (prefixWord ++ tailWord_646417).sum := by decide
  have hdescent : baseEnd_646417 < baseStart_646417 := by decide
  rcases family_descends (prefixWord ++ tailWord_646417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646690 : List Nat := [3, 3, 1, 1, 1, 1, 6, 5]
def baseStart_646690 : Nat := 118140960795 + 646690 * 2 ^ 59
def prefixEnd_646690 : Nat := 4983230072969 + 3 ^ 40 * 646690 * 2
def baseEnd_646690 : Nat := 49194489549063712014953

theorem tailTrace_646690 : CollatzResearch.WordTrace tailWord_646690 prefixEnd_646690 49194489549063712014953 := by
  unfold tailWord_646690
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896680506790012676016381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15724481351440033802710349 5896680506790012676016381)
  ·
    refine ⟨2211255190046254753506143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5896680506790012676016381 2211255190046254753506143)
    ·
      refine ⟨3316882785069382130259215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2211255190046254753506143 3316882785069382130259215)
      ·
        refine ⟨4975324177604073195388823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3316882785069382130259215 4975324177604073195388823)
        ·
          refine ⟨7462986266406109793083235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4975324177604073195388823 7462986266406109793083235)
          ·
            refine ⟨11194479399609164689624853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7462986266406109793083235 11194479399609164689624853)
            ·
              refine ⟨524741221856679594826165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11194479399609164689624853 524741221856679594826165)
              ·
                refine ⟨49194489549063712014953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 524741221856679594826165 49194489549063712014953)
                ·
                  rfl

theorem cell21_646690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_646690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646690 prefixEnd_646690 := by exact prefixLift 646690
  have htrace : WordTrace (prefixWord ++ tailWord_646690) baseStart_646690 baseEnd_646690 := by
    simpa [prefixWord, tailWord_646690, baseEnd_646690] using wordTrace_append hprefix tailTrace_646690
  have hstable : (prefixWord ++ tailWord_646690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646690).length < 2 ^ (prefixWord ++ tailWord_646690).sum := by decide
  have hdescent : baseEnd_646690 < baseStart_646690 := by decide
  rcases family_descends (prefixWord ++ tailWord_646690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646696 : List Nat := [2, 1, 5, 2, 3, 1, 1, 3, 3]
def baseStart_646696 : Nat := 118140960795 + 646696 * 2 ^ 59
def prefixEnd_646696 : Nat := 4983230072969 + 3 ^ 40 * 646696 * 2
def baseEnd_646696 : Nat := 147584837928936458944847

theorem tailTrace_646696 : CollatzResearch.WordTrace tailWord_646696 prefixEnd_646696 147584837928936458944847 := by
  unfold tailWord_646696
  simp only [CollatzResearch.WordTrace]
  refine ⟨11793470432569156864391971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15724627243425542485855961 11793470432569156864391971)
  ·
    refine ⟨17690205648853735296587957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11793470432569156864391971 17690205648853735296587957)
    ·
      refine ⟨1658456779580037684055121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17690205648853735296587957 1658456779580037684055121)
      ·
        refine ⟨1243842584685028263041341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1658456779580037684055121 1243842584685028263041341)
        ·
          refine ⟨466440969256885598640503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1243842584685028263041341 466440969256885598640503)
          ·
            refine ⟨699661453885328397960755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466440969256885598640503 699661453885328397960755)
            ·
              refine ⟨1049492180827992596941133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699661453885328397960755 1049492180827992596941133)
              ·
                refine ⟨393559567810497223852925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1049492180827992596941133 393559567810497223852925)
                ·
                  refine ⟨147584837928936458944847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393559567810497223852925 147584837928936458944847)
                  ·
                    rfl

theorem cell21_646696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 3].length) (baseStart_646696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646696 prefixEnd_646696 := by exact prefixLift 646696
  have htrace : WordTrace (prefixWord ++ tailWord_646696) baseStart_646696 baseEnd_646696 := by
    simpa [prefixWord, tailWord_646696, baseEnd_646696] using wordTrace_append hprefix tailTrace_646696
  have hstable : (prefixWord ++ tailWord_646696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646696).length < 2 ^ (prefixWord ++ tailWord_646696).sum := by decide
  have hdescent : baseEnd_646696 < baseStart_646696 := by decide
  rcases family_descends (prefixWord ++ tailWord_646696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646766 : List Nat := [4, 1, 2, 2, 4, 8]
def baseStart_646766 : Nat := 118140960795 + 646766 * 2 ^ 59
def prefixEnd_646766 : Nat := 4983230072969 + 3 ^ 40 * 646766 * 2
def baseEnd_646766 : Nat := 5466696773430810843631

theorem tailTrace_646766 : CollatzResearch.WordTrace tailWord_646766 prefixEnd_646766 5466696773430810843631 := by
  unfold tailWord_646766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2948686746860589460479019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15726329316589810455888101 2948686746860589460479019)
  ·
    refine ⟨4423030120290884190718529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2948686746860589460479019 4423030120290884190718529)
    ·
      refine ⟨3317272590218163143038897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4423030120290884190718529 3317272590218163143038897)
      ·
        refine ⟨2487954442663622357279173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3317272590218163143038897 2487954442663622357279173)
        ·
          refine ⟨466491457999429191989845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2487954442663622357279173 466491457999429191989845)
          ·
            refine ⟨5466696773430810843631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 466491457999429191989845 5466696773430810843631)
            ·
              rfl

theorem cell21_646766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 8].length) (baseStart_646766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646766 prefixEnd_646766 := by exact prefixLift 646766
  have htrace : WordTrace (prefixWord ++ tailWord_646766) baseStart_646766 baseEnd_646766 := by
    simpa [prefixWord, tailWord_646766, baseEnd_646766] using wordTrace_append hprefix tailTrace_646766
  have hstable : (prefixWord ++ tailWord_646766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646766).length < 2 ^ (prefixWord ++ tailWord_646766).sum := by decide
  have hdescent : baseEnd_646766 < baseStart_646766 := by decide
  rcases family_descends (prefixWord ++ tailWord_646766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646814 : List Nat := [4, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_646814 : Nat := 118140960795 + 646814 * 2 ^ 59
def prefixEnd_646814 : Nat := 4983230072969 + 3 ^ 40 * 646814 * 2
def baseEnd_646814 : Nat := 147611767136594475977939

theorem tailTrace_646814 : CollatzResearch.WordTrace tailWord_646814 prefixEnd_646814 147611767136594475977939 := by
  unfold tailWord_646814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2948905584838852485197437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15727496452473879921052997 2948905584838852485197437)
  ·
    refine ⟨1105839594314569681949039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2948905584838852485197437 1105839594314569681949039)
    ·
      refine ⟨1658759391471854522923559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1105839594314569681949039 1658759391471854522923559)
      ·
        refine ⟨2488139087207781784385339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1658759391471854522923559 2488139087207781784385339)
        ·
          refine ⟨3732208630811672676578009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2488139087207781784385339 3732208630811672676578009)
          ·
            refine ⟨2799156473108754507433507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3732208630811672676578009 2799156473108754507433507)
            ·
              refine ⟨4198734709663131761150261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2799156473108754507433507 4198734709663131761150261)
              ·
                refine ⟨393631379030918602607837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4198734709663131761150261 393631379030918602607837)
                ·
                  refine ⟨147611767136594475977939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393631379030918602607837 147611767136594475977939)
                  ·
                    rfl

theorem cell21_646814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_646814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646814 prefixEnd_646814 := by exact prefixLift 646814
  have htrace : WordTrace (prefixWord ++ tailWord_646814) baseStart_646814 baseEnd_646814 := by
    simpa [prefixWord, tailWord_646814, baseEnd_646814] using wordTrace_append hprefix tailTrace_646814
  have hstable : (prefixWord ++ tailWord_646814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646814).length < 2 ^ (prefixWord ++ tailWord_646814).sum := by decide
  have hdescent : baseEnd_646814 < baseStart_646814 := by decide
  rcases family_descends (prefixWord ++ tailWord_646814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646873 : List Nat := [1, 2, 1, 2, 3, 3, 3, 3, 3]
def baseStart_646873 : Nat := 118140960795 + 646873 * 2 ^ 59
def prefixEnd_646873 : Nat := 4983230072969 + 3 ^ 40 * 646873 * 2
def baseEnd_646873 : Nat := 147625231740423484494485

theorem tailTrace_646873 : CollatzResearch.WordTrace tailWord_646873 prefixEnd_646873 147625231740423484494485 := by
  unfold tailWord_646873
  simp only [CollatzResearch.WordTrace]
  refine ⟨23593396585497072957977273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15728931056998048638651515 23593396585497072957977273)
  ·
    refine ⟨17695047439122804718482955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23593396585497072957977273 17695047439122804718482955)
    ·
      refine ⟨26542571158684207077724433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17695047439122804718482955 26542571158684207077724433)
      ·
        refine ⟨19906928369013155308293325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26542571158684207077724433 19906928369013155308293325)
        ·
          refine ⟨7465098138379933240609997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19906928369013155308293325 7465098138379933240609997)
          ·
            refine ⟨2799411801892474965228749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7465098138379933240609997 2799411801892474965228749)
            ·
              refine ⟨1049779425709678111960781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2799411801892474965228749 1049779425709678111960781)
              ·
                refine ⟨393667284641129291985293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1049779425709678111960781 393667284641129291985293)
                ·
                  refine ⟨147625231740423484494485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393667284641129291985293 147625231740423484494485)
                  ·
                    rfl

theorem cell21_646873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 3].length) (baseStart_646873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646873 prefixEnd_646873 := by exact prefixLift 646873
  have htrace : WordTrace (prefixWord ++ tailWord_646873) baseStart_646873 baseEnd_646873 := by
    simpa [prefixWord, tailWord_646873, baseEnd_646873] using wordTrace_append hprefix tailTrace_646873
  have hstable : (prefixWord ++ tailWord_646873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646873).length < 2 ^ (prefixWord ++ tailWord_646873).sum := by decide
  have hdescent : baseEnd_646873 < baseStart_646873 := by decide
  rcases family_descends (prefixWord ++ tailWord_646873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646915 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 5]
def baseStart_646915 : Nat := 118140960795 + 646915 * 2 ^ 59
def prefixEnd_646915 : Nat := 4983230072969 + 3 ^ 40 * 646915 * 2
def baseEnd_646915 : Nat := 147634816712640744794399

theorem tailTrace_646915 : CollatzResearch.WordTrace tailWord_646915 prefixEnd_646915 147634816712640744794399 := by
  unfold tailWord_646915
  simp only [CollatzResearch.WordTrace]
  refine ⟨23594928451344914131006199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15729952300896609420670799 23594928451344914131006199)
  ·
    refine ⟨35392392677017371196509299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23594928451344914131006199 35392392677017371196509299)
    ·
      refine ⟨53088589015526056794763949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35392392677017371196509299 53088589015526056794763949)
      ·
        refine ⟨19908220880822271298036481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53088589015526056794763949 19908220880822271298036481)
        ·
          refine ⟨14931165660616703473527361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19908220880822271298036481 14931165660616703473527361)
          ·
            refine ⟨11198374245462527605145521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14931165660616703473527361 11198374245462527605145521)
            ·
              refine ⟨8398780684096895703859141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11198374245462527605145521 8398780684096895703859141)
              ·
                refine ⟨1574771378268167944473589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8398780684096895703859141 1574771378268167944473589)
                ·
                  refine ⟨147634816712640744794399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1574771378268167944473589 147634816712640744794399)
                  ·
                    rfl

theorem cell21_646915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_646915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646915 prefixEnd_646915 := by exact prefixLift 646915
  have htrace : WordTrace (prefixWord ++ tailWord_646915) baseStart_646915 baseEnd_646915 := by
    simpa [prefixWord, tailWord_646915, baseEnd_646915] using wordTrace_append hprefix tailTrace_646915
  have hstable : (prefixWord ++ tailWord_646915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646915).length < 2 ^ (prefixWord ++ tailWord_646915).sum := by decide
  have hdescent : baseEnd_646915 < baseStart_646915 := by decide
  rcases family_descends (prefixWord ++ tailWord_646915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646949 : List Nat := [1, 3, 1, 2, 3, 3, 1, 4, 3]
def baseStart_646949 : Nat := 118140960795 + 646949 * 2 ^ 59
def prefixEnd_646949 : Nat := 4983230072969 + 3 ^ 40 * 646949 * 2
def baseEnd_646949 : Nat := 147642575975864241227663

theorem tailTrace_646949 : CollatzResearch.WordTrace tailWord_646949 prefixEnd_646949 147642575975864241227663 := by
  unfold tailWord_646949
  simp only [CollatzResearch.WordTrace]
  refine ⟨23596168533221737937743901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15730779022147825291829267 23596168533221737937743901)
  ·
    refine ⟨8848563199958151726653963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23596168533221737937743901 8848563199958151726653963)
    ·
      refine ⟨13272844799937227589980945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8848563199958151726653963 13272844799937227589980945)
      ·
        refine ⟨9954633599952920692485709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13272844799937227589980945 9954633599952920692485709)
        ·
          refine ⟨3732987599982345259682141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9954633599952920692485709 3732987599982345259682141)
          ·
            refine ⟨1399870349993379472380803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3732987599982345259682141 1399870349993379472380803)
            ·
              refine ⟨2099805524990069208571205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399870349993379472380803 2099805524990069208571205)
              ·
                refine ⟨393713535935637976607101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2099805524990069208571205 393713535935637976607101)
                ·
                  refine ⟨147642575975864241227663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393713535935637976607101 147642575975864241227663)
                  ·
                    rfl

theorem cell21_646949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_646949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_646949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_646949 prefixEnd_646949 := by exact prefixLift 646949
  have htrace : WordTrace (prefixWord ++ tailWord_646949) baseStart_646949 baseEnd_646949 := by
    simpa [prefixWord, tailWord_646949, baseEnd_646949] using wordTrace_append hprefix tailTrace_646949
  have hstable : (prefixWord ++ tailWord_646949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646949).length < 2 ^ (prefixWord ++ tailWord_646949).sum := by decide
  have hdescent : baseEnd_646949 < baseStart_646949 := by decide
  rcases family_descends (prefixWord ++ tailWord_646949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647008 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 5]
def baseStart_647008 : Nat := 118140960795 + 647008 * 2 ^ 59
def prefixEnd_647008 : Nat := 4983230072969 + 3 ^ 40 * 647008 * 2
def baseEnd_647008 : Nat := 147656040579693249744209

theorem tailTrace_647008 : CollatzResearch.WordTrace tailWord_647008 prefixEnd_647008 147656040579693249744209 := by
  unfold tailWord_647008
  simp only [CollatzResearch.WordTrace]
  refine ⟨11799160220003995507070839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15732213626671994009427785 11799160220003995507070839)
  ·
    refine ⟨17698740330005993260606259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11799160220003995507070839 17698740330005993260606259)
    ·
      refine ⟨26548110495008989890909389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17698740330005993260606259 26548110495008989890909389)
      ·
        refine ⟨9955541435628371209091021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26548110495008989890909389 9955541435628371209091021)
        ·
          refine ⟨3733328038360639203409133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9955541435628371209091021 3733328038360639203409133)
          ·
            refine ⟨1399998014385239701278425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3733328038360639203409133 1399998014385239701278425)
            ·
              refine ⟨1049998510788929775958819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1399998014385239701278425 1049998510788929775958819)
              ·
                refine ⟨1574997766183394663938229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049998510788929775958819 1574997766183394663938229)
                ·
                  refine ⟨147656040579693249744209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1574997766183394663938229 147656040579693249744209)
                  ·
                    rfl

theorem cell21_647008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_647008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647008 prefixEnd_647008 := by exact prefixLift 647008
  have htrace : WordTrace (prefixWord ++ tailWord_647008) baseStart_647008 baseEnd_647008 := by
    simpa [prefixWord, tailWord_647008, baseEnd_647008] using wordTrace_append hprefix tailTrace_647008
  have hstable : (prefixWord ++ tailWord_647008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647008).length < 2 ^ (prefixWord ++ tailWord_647008).sum := by decide
  have hdescent : baseEnd_647008 < baseStart_647008 := by decide
  rcases family_descends (prefixWord ++ tailWord_647008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647073 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 4]
def baseStart_647073 : Nat := 118140960795 + 647073 * 2 ^ 59
def prefixEnd_647073 : Nat := 4983230072969 + 3 ^ 40 * 647073 * 2
def baseEnd_647073 : Nat := 147670874465267581160743

theorem tailTrace_647073 : CollatzResearch.WordTrace tailWord_647073 prefixEnd_647073 147670874465267581160743 := by
  unfold tailWord_647073
  simp only [CollatzResearch.WordTrace]
  refine ⟨23600691184772507115257873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15733794123181671410171915 23600691184772507115257873)
  ·
    refine ⟨17700518388579380336443405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23600691184772507115257873 17700518388579380336443405)
    ·
      refine ⟨6637694395717267626166277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17700518388579380336443405 6637694395717267626166277)
      ·
        refine ⟨1244567699196987679906177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6637694395717267626166277 1244567699196987679906177)
        ·
          refine ⟨933425774397740759929633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1244567699196987679906177 933425774397740759929633)
          ·
            refine ⟨700069330798305569947225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933425774397740759929633 700069330798305569947225)
            ·
              refine ⟨525051998098729177460419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700069330798305569947225 525051998098729177460419)
              ·
                refine ⟨787577997148093766190629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525051998098729177460419 787577997148093766190629)
                ·
                  refine ⟨147670874465267581160743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 787577997148093766190629 147670874465267581160743)
                  ·
                    rfl

theorem cell21_647073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_647073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647073 prefixEnd_647073 := by exact prefixLift 647073
  have htrace : WordTrace (prefixWord ++ tailWord_647073) baseStart_647073 baseEnd_647073 := by
    simpa [prefixWord, tailWord_647073, baseEnd_647073] using wordTrace_append hprefix tailTrace_647073
  have hstable : (prefixWord ++ tailWord_647073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647073).length < 2 ^ (prefixWord ++ tailWord_647073).sum := by decide
  have hdescent : baseEnd_647073 < baseStart_647073 := by decide
  rcases family_descends (prefixWord ++ tailWord_647073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647081 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 8]
def baseStart_647081 : Nat := 118140960795 + 647081 * 2 ^ 59
def prefixEnd_647081 : Nat := 4983230072969 + 3 ^ 40 * 647081 * 2
def baseEnd_647081 : Nat := 147672700174261345027393

theorem tailTrace_647081 : CollatzResearch.WordTrace tailWord_647081 prefixEnd_647081 147672700174261345027393 := by
  unfold tailWord_647081
  simp only [CollatzResearch.WordTrace]
  refine ⟨23600982968743524481549097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15733988645829016321032731 23600982968743524481549097)
  ·
    refine ⟨17700737226557643361161823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23600982968743524481549097 17700737226557643361161823)
    ·
      refine ⟨26551105839836465041742735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17700737226557643361161823 26551105839836465041742735)
      ·
        refine ⟨39826658759754697562614103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26551105839836465041742735 39826658759754697562614103)
        ·
          refine ⟨59739988139632046343921155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39826658759754697562614103 59739988139632046343921155)
          ·
            refine ⟨89609982209448069515881733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59739988139632046343921155 89609982209448069515881733)
            ·
              refine ⟨16801871664271513034227825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89609982209448069515881733 16801871664271513034227825)
              ·
                refine ⟨12601403748203634775670869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16801871664271513034227825 12601403748203634775670869)
                ·
                  refine ⟨147672700174261345027393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12601403748203634775670869 147672700174261345027393)
                  ·
                    rfl

theorem cell21_647081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_647081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647081 prefixEnd_647081 := by exact prefixLift 647081
  have htrace : WordTrace (prefixWord ++ tailWord_647081) baseStart_647081 baseEnd_647081 := by
    simpa [prefixWord, tailWord_647081, baseEnd_647081] using wordTrace_append hprefix tailTrace_647081
  have hstable : (prefixWord ++ tailWord_647081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647081).length < 2 ^ (prefixWord ++ tailWord_647081).sum := by decide
  have hdescent : baseEnd_647081 < baseStart_647081 := by decide
  rcases family_descends (prefixWord ++ tailWord_647081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647112 : List Nat := [2, 1, 3, 1, 4, 10]
def baseStart_647112 : Nat := 118140960795 + 647112 * 2 ^ 59
def prefixEnd_647112 : Nat := 4983230072969 + 3 ^ 40 * 647112 * 2
def baseEnd_647112 : Nat := 5469621288763414074469

theorem tailTrace_647112 : CollatzResearch.WordTrace tailWord_647112 prefixEnd_647112 5469621288763414074469 := by
  unfold tailWord_647112
  simp only [CollatzResearch.WordTrace]
  refine ⟨11801056815815608387963795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15734742421087477850618393 11801056815815608387963795)
  ·
    refine ⟨17701585223723412581945693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11801056815815608387963795 17701585223723412581945693)
    ·
      refine ⟨6638094458896279718229635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17701585223723412581945693 6638094458896279718229635)
      ·
        refine ⟨9957141688344419577344453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6638094458896279718229635 9957141688344419577344453)
        ·
          refine ⟨1866964066564578670752085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9957141688344419577344453 1866964066564578670752085)
          ·
            refine ⟨5469621288763414074469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1866964066564578670752085 5469621288763414074469)
            ·
              rfl

theorem cell21_647112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 10].length) (baseStart_647112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647112 prefixEnd_647112 := by exact prefixLift 647112
  have htrace : WordTrace (prefixWord ++ tailWord_647112) baseStart_647112 baseEnd_647112 := by
    simpa [prefixWord, tailWord_647112, baseEnd_647112] using wordTrace_append hprefix tailTrace_647112
  have hstable : (prefixWord ++ tailWord_647112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647112).length < 2 ^ (prefixWord ++ tailWord_647112).sum := by decide
  have hdescent : baseEnd_647112 < baseStart_647112 := by decide
  rcases family_descends (prefixWord ++ tailWord_647112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647160 : List Nat := [2, 1, 2, 1, 1, 3, 3, 5, 3]
def baseStart_647160 : Nat := 118140960795 + 647160 * 2 ^ 59
def prefixEnd_647160 : Nat := 4983230072969 + 3 ^ 40 * 647160 * 2
def baseEnd_647160 : Nat := 147690729050574763210565

theorem tailTrace_647160 : CollatzResearch.WordTrace tailWord_647160 prefixEnd_647160 147690729050574763210565 := by
  unfold tailWord_647160
  simp only [CollatzResearch.WordTrace]
  refine ⟨11801932167728660486837467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15735909556971547315783289 11801932167728660486837467)
  ·
    refine ⟨17702898251592990730256201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11801932167728660486837467 17702898251592990730256201)
    ·
      refine ⟨13277173688694743047692151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17702898251592990730256201 13277173688694743047692151)
      ·
        refine ⟨19915760533042114571538227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13277173688694743047692151 19915760533042114571538227)
        ·
          refine ⟨29873640799563171857307341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19915760533042114571538227 29873640799563171857307341)
          ·
            refine ⟨11202615299836189446490253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29873640799563171857307341 11202615299836189446490253)
            ·
              refine ⟨4200980737438571042433845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11202615299836189446490253 4200980737438571042433845)
              ·
                refine ⟨393841944134866035228173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4200980737438571042433845 393841944134866035228173)
                ·
                  refine ⟨147690729050574763210565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393841944134866035228173 147690729050574763210565)
                  ·
                    rfl

theorem cell21_647160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 3].length) (baseStart_647160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647160 prefixEnd_647160 := by exact prefixLift 647160
  have htrace : WordTrace (prefixWord ++ tailWord_647160) baseStart_647160 baseEnd_647160 := by
    simpa [prefixWord, tailWord_647160, baseEnd_647160] using wordTrace_append hprefix tailTrace_647160
  have hstable : (prefixWord ++ tailWord_647160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647160).length < 2 ^ (prefixWord ++ tailWord_647160).sum := by decide
  have hdescent : baseEnd_647160 < baseStart_647160 := by decide
  rcases family_descends (prefixWord ++ tailWord_647160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647205 : List Nat := [1, 3, 1, 2, 2, 3, 4, 5]
def baseStart_647205 : Nat := 118140960795 + 647205 * 2 ^ 59
def prefixEnd_647205 : Nat := 4983230072969 + 3 ^ 40 * 647205 * 2
def baseEnd_647205 : Nat := 49233666221221561653491

theorem tailTrace_647205 : CollatzResearch.WordTrace tailWord_647205 prefixEnd_647205 49233666221221561653491 := by
  unfold tailWord_647205
  simp only [CollatzResearch.WordTrace]
  refine ⟨23605505620294293659063069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15737003746862862439375379 23605505620294293659063069)
  ·
    refine ⟨8852064607610360122148651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23605505620294293659063069 8852064607610360122148651)
    ·
      refine ⟨13278096911415540183222977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8852064607610360122148651 13278096911415540183222977)
      ·
        refine ⟨9958572683561655137417233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13278096911415540183222977 9958572683561655137417233)
        ·
          refine ⟨7468929512671241353062925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9958572683561655137417233 7468929512671241353062925)
          ·
            refine ⟨2800848567251715507398597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7468929512671241353062925 2800848567251715507398597)
            ·
              refine ⟨525159106359696657637237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2800848567251715507398597 525159106359696657637237)
              ·
                refine ⟨49233666221221561653491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 525159106359696657637237 49233666221221561653491)
                ·
                  rfl

theorem cell21_647205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 5].length) (baseStart_647205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647205 prefixEnd_647205 := by exact prefixLift 647205
  have htrace : WordTrace (prefixWord ++ tailWord_647205) baseStart_647205 baseEnd_647205 := by
    simpa [prefixWord, tailWord_647205, baseEnd_647205] using wordTrace_append hprefix tailTrace_647205
  have hstable : (prefixWord ++ tailWord_647205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647205).length < 2 ^ (prefixWord ++ tailWord_647205).sum := by decide
  have hdescent : baseEnd_647205 < baseStart_647205 := by decide
  rcases family_descends (prefixWord ++ tailWord_647205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647264 : List Nat := [2, 1, 1, 3, 2, 3, 2, 7]
def baseStart_647264 : Nat := 118140960795 + 647264 * 2 ^ 59
def prefixEnd_647264 : Nat := 4983230072969 + 3 ^ 40 * 647264 * 2
def baseEnd_647264 : Nat := 49238154422497897825673

theorem tailTrace_647264 : CollatzResearch.WordTrace tailWord_647264 prefixEnd_647264 49238154422497897825673 := by
  unfold tailWord_647264
  simp only [CollatzResearch.WordTrace]
  refine ⟨11803828763540273367730423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15738438351387031156973897 11803828763540273367730423)
  ·
    refine ⟨17705743145310410051595635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11803828763540273367730423 17705743145310410051595635)
    ·
      refine ⟨26558614717965615077393453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17705743145310410051595635 26558614717965615077393453)
      ·
        refine ⟨9959480519237105654022545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26558614717965615077393453 9959480519237105654022545)
        ·
          refine ⟨7469610389427829240516909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9959480519237105654022545 7469610389427829240516909)
          ·
            refine ⟨2801103896035435965193841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7469610389427829240516909 2801103896035435965193841)
            ·
              refine ⟨2100827922026576973895381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2801103896035435965193841 2100827922026576973895381)
              ·
                refine ⟨49238154422497897825673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2100827922026576973895381 49238154422497897825673)
                ·
                  rfl

theorem cell21_647264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_647264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647264 prefixEnd_647264 := by exact prefixLift 647264
  have htrace : WordTrace (prefixWord ++ tailWord_647264) baseStart_647264 baseEnd_647264 := by
    simpa [prefixWord, tailWord_647264, baseEnd_647264] using wordTrace_append hprefix tailTrace_647264
  have hstable : (prefixWord ++ tailWord_647264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647264).length < 2 ^ (prefixWord ++ tailWord_647264).sum := by decide
  have hdescent : baseEnd_647264 < baseStart_647264 := by decide
  rcases family_descends (prefixWord ++ tailWord_647264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647329 : List Nat := [1, 2, 3, 3, 1, 3, 2, 3, 3]
def baseStart_647329 : Nat := 118140960795 + 647329 * 2 ^ 59
def prefixEnd_647329 : Nat := 4983230072969 + 3 ^ 40 * 647329 * 2
def baseEnd_647329 : Nat := 147729297153068024893553

theorem tailTrace_647329 : CollatzResearch.WordTrace tailWord_647329 prefixEnd_647329 147729297153068024893553 := by
  unfold tailWord_647329
  simp only [CollatzResearch.WordTrace]
  refine ⟨23610028271845062836577041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15740018847896708557718027 23610028271845062836577041)
  ·
    refine ⟨17707521203883797127432781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23610028271845062836577041 17707521203883797127432781)
    ·
      refine ⟨6640320451456423922787293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17707521203883797127432781 6640320451456423922787293)
      ·
        refine ⟨2490120169296158971045235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6640320451456423922787293 2490120169296158971045235)
        ·
          refine ⟨3735180253944238456567853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490120169296158971045235 3735180253944238456567853)
          ·
            refine ⟨1400692595229089421212945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3735180253944238456567853 1400692595229089421212945)
            ·
              refine ⟨1050519446421817065909709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1400692595229089421212945 1050519446421817065909709)
              ·
                refine ⟨393944792408181399716141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1050519446421817065909709 393944792408181399716141)
                ·
                  refine ⟨147729297153068024893553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393944792408181399716141 147729297153068024893553)
                  ·
                    rfl

theorem cell21_647329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 3].length) (baseStart_647329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647329 prefixEnd_647329 := by exact prefixLift 647329
  have htrace : WordTrace (prefixWord ++ tailWord_647329) baseStart_647329 baseEnd_647329 := by
    simpa [prefixWord, tailWord_647329, baseEnd_647329] using wordTrace_append hprefix tailTrace_647329
  have hstable : (prefixWord ++ tailWord_647329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647329).length < 2 ^ (prefixWord ++ tailWord_647329).sum := by decide
  have hdescent : baseEnd_647329 < baseStart_647329 := by decide
  rcases family_descends (prefixWord ++ tailWord_647329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647374 : List Nat := [4, 1, 1, 1, 4, 3, 2, 5]
def baseStart_647374 : Nat := 118140960795 + 647374 * 2 ^ 59
def prefixEnd_647374 : Nat := 4983230072969 + 3 ^ 40 * 647374 * 2
def baseEnd_647374 : Nat := 49246522255385982214487

theorem tailTrace_647374 : CollatzResearch.WordTrace tailWord_647374 prefixEnd_647374 49246522255385982214487 := by
  unfold tailWord_647374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2951458694585254440245647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15741113037788023681310117 2951458694585254440245647)
  ·
    refine ⟨4427188041877881660368471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2951458694585254440245647 4427188041877881660368471)
    ·
      refine ⟨6640782062816822490552707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4427188041877881660368471 6640782062816822490552707)
      ·
        refine ⟨9961173094225233735829061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6640782062816822490552707 9961173094225233735829061)
        ·
          refine ⟨1867719955167231325467949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9961173094225233735829061 1867719955167231325467949)
          ·
            refine ⟨700394983187711747050481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1867719955167231325467949 700394983187711747050481)
            ·
              refine ⟨525296237390783810287861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700394983187711747050481 525296237390783810287861)
              ·
                refine ⟨49246522255385982214487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 525296237390783810287861 49246522255385982214487)
                ·
                  rfl

theorem cell21_647374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_647374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647374 prefixEnd_647374 := by exact prefixLift 647374
  have htrace : WordTrace (prefixWord ++ tailWord_647374) baseStart_647374 baseEnd_647374 := by
    simpa [prefixWord, tailWord_647374, baseEnd_647374] using wordTrace_append hprefix tailTrace_647374
  have hstable : (prefixWord ++ tailWord_647374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647374).length < 2 ^ (prefixWord ++ tailWord_647374).sum := by decide
  have hdescent : baseEnd_647374 < baseStart_647374 := by decide
  rcases family_descends (prefixWord ++ tailWord_647374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647385 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 6]
def baseStart_647385 : Nat := 118140960795 + 647385 * 2 ^ 59
def prefixEnd_647385 : Nat := 4983230072969 + 3 ^ 40 * 647385 * 2
def baseEnd_647385 : Nat := 147742077116024371960105

theorem tailTrace_647385 : CollatzResearch.WordTrace tailWord_647385 prefixEnd_647385 147742077116024371960105 := by
  unfold tailWord_647385
  simp only [CollatzResearch.WordTrace]
  refine ⟨23612070759642184400615609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15741380506428122933743739 23612070759642184400615609)
  ·
    refine ⟨17709053069731638300461707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23612070759642184400615609 17709053069731638300461707)
    ·
      refine ⟨26563579604597457450692561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17709053069731638300461707 26563579604597457450692561)
      ·
        refine ⟨19922684703448093088019421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26563579604597457450692561 19922684703448093088019421)
        ·
          refine ⟨7471006763793034908007283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19922684703448093088019421 7471006763793034908007283)
          ·
            refine ⟨11206510145689552362010925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7471006763793034908007283 11206510145689552362010925)
            ·
              refine ⟨4202441304633582135754097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11206510145689552362010925 4202441304633582135754097)
              ·
                refine ⟨3151830978475186601815573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4202441304633582135754097 3151830978475186601815573)
                ·
                  refine ⟨147742077116024371960105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3151830978475186601815573 147742077116024371960105)
                  ·
                    rfl

theorem cell21_647385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_647385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647385 prefixEnd_647385 := by exact prefixLift 647385
  have htrace : WordTrace (prefixWord ++ tailWord_647385) baseStart_647385 baseEnd_647385 := by
    simpa [prefixWord, tailWord_647385, baseEnd_647385] using wordTrace_append hprefix tailTrace_647385
  have hstable : (prefixWord ++ tailWord_647385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647385).length < 2 ^ (prefixWord ++ tailWord_647385).sum := by decide
  have hdescent : baseEnd_647385 < baseStart_647385 := by decide
  rcases family_descends (prefixWord ++ tailWord_647385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647402 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_647402 : Nat := 118140960795 + 647402 * 2 ^ 59
def prefixEnd_647402 : Nat := 4983230072969 + 3 ^ 40 * 647402 * 2
def baseEnd_647402 : Nat := 147745956747636120176737

theorem tailTrace_647402 : CollatzResearch.WordTrace tailWord_647402 prefixEnd_647402 147745956747636120176737 := by
  unfold tailWord_647402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5903172700145149075996115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15741793867053730869322973 5903172700145149075996115)
  ·
    refine ⟨8854759050217723613994173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5903172700145149075996115 8854759050217723613994173)
    ·
      refine ⟨3320534643831646355247815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8854759050217723613994173 3320534643831646355247815)
      ·
        refine ⟨4980801965747469532871723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3320534643831646355247815 4980801965747469532871723)
        ·
          refine ⟨7471202948621204299307585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4980801965747469532871723 7471202948621204299307585)
          ·
            refine ⟨5603402211465903224480689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7471202948621204299307585 5603402211465903224480689)
            ·
              refine ⟨4202551658599427418360517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5603402211465903224480689 4202551658599427418360517)
              ·
                refine ⟨787978435987392640942597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4202551658599427418360517 787978435987392640942597)
                ·
                  refine ⟨147745956747636120176737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 787978435987392640942597 147745956747636120176737)
                  ·
                    rfl

theorem cell21_647402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_647402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647402 prefixEnd_647402 := by exact prefixLift 647402
  have htrace : WordTrace (prefixWord ++ tailWord_647402) baseStart_647402 baseEnd_647402 := by
    simpa [prefixWord, tailWord_647402, baseEnd_647402] using wordTrace_append hprefix tailTrace_647402
  have hstable : (prefixWord ++ tailWord_647402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647402).length < 2 ^ (prefixWord ++ tailWord_647402).sum := by decide
  have hdescent : baseEnd_647402 < baseStart_647402 := by decide
  rcases family_descends (prefixWord ++ tailWord_647402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647405 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 5]
def baseStart_647405 : Nat := 118140960795 + 647405 * 2 ^ 59
def prefixEnd_647405 : Nat := 4983230072969 + 3 ^ 40 * 647405 * 2
def baseEnd_647405 : Nat := 147746641388508781626731

theorem tailTrace_647405 : CollatzResearch.WordTrace tailWord_647405 prefixEnd_647405 147746641388508781626731 := by
  unfold tailWord_647405
  simp only [CollatzResearch.WordTrace]
  refine ⟨23612800219569727816343669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15741866813046485210895779 23612800219569727816343669)
  ·
    refine ⟨2213700020584661982782219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23612800219569727816343669 2213700020584661982782219)
    ·
      refine ⟨3320550030876992974173329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2213700020584661982782219 3320550030876992974173329)
      ·
        refine ⟨2490412523157744730629997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3320550030876992974173329 2490412523157744730629997)
        ·
          refine ⟨933904696184154273986249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2490412523157744730629997 933904696184154273986249)
          ·
            refine ⟨700428522138115705489687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933904696184154273986249 700428522138115705489687)
            ·
              refine ⟨1050642783207173558234531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700428522138115705489687 1050642783207173558234531)
              ·
                refine ⟨1575964174810760337351797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050642783207173558234531 1575964174810760337351797)
                ·
                  refine ⟨147746641388508781626731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1575964174810760337351797 147746641388508781626731)
                  ·
                    rfl

theorem cell21_647405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_647405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647405 prefixEnd_647405 := by exact prefixLift 647405
  have htrace : WordTrace (prefixWord ++ tailWord_647405) baseStart_647405 baseEnd_647405 := by
    simpa [prefixWord, tailWord_647405, baseEnd_647405] using wordTrace_append hprefix tailTrace_647405
  have hstable : (prefixWord ++ tailWord_647405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647405).length < 2 ^ (prefixWord ++ tailWord_647405).sum := by decide
  have hdescent : baseEnd_647405 < baseStart_647405 := by decide
  rcases family_descends (prefixWord ++ tailWord_647405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647523 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 5]
def baseStart_647523 : Nat := 118140960795 + 647523 * 2 ^ 59
def prefixEnd_647523 : Nat := 4983230072969 + 3 ^ 40 * 647523 * 2
def baseEnd_647523 : Nat := 147773570596166798659823

theorem tailTrace_647523 : CollatzResearch.WordTrace tailWord_647523 prefixEnd_647523 147773570596166798659823 := by
  unfold tailWord_647523
  simp only [CollatzResearch.WordTrace]
  refine ⟨23617104033142233969139223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15744736022094822646092815 23617104033142233969139223)
  ·
    refine ⟨35425656049713350953708835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23617104033142233969139223 35425656049713350953708835)
    ·
      refine ⟨53138484074570026430563253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35425656049713350953708835 53138484074570026430563253)
      ·
        refine ⟨4981732881990939977865305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53138484074570026430563253 4981732881990939977865305)
        ·
          refine ⟨3736299661493204983398979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4981732881990939977865305 3736299661493204983398979)
          ·
            refine ⟨5604449492239807475098469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3736299661493204983398979 5604449492239807475098469)
            ·
              refine ⟨1050834279794963901580963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5604449492239807475098469 1050834279794963901580963)
              ·
                refine ⟨1576251419692445852371445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050834279794963901580963 1576251419692445852371445)
                ·
                  refine ⟨147773570596166798659823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1576251419692445852371445 147773570596166798659823)
                  ·
                    rfl

theorem cell21_647523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 5].length) (baseStart_647523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647523 prefixEnd_647523 := by exact prefixLift 647523
  have htrace : WordTrace (prefixWord ++ tailWord_647523) baseStart_647523 baseEnd_647523 := by
    simpa [prefixWord, tailWord_647523, baseEnd_647523] using wordTrace_append hprefix tailTrace_647523
  have hstable : (prefixWord ++ tailWord_647523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647523).length < 2 ^ (prefixWord ++ tailWord_647523).sum := by decide
  have hdescent : baseEnd_647523 < baseStart_647523 := by decide
  rcases family_descends (prefixWord ++ tailWord_647523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647551 : List Nat := [1, 1, 2, 2, 1, 1, 2, 11]
def baseStart_647551 : Nat := 118140960795 + 647551 * 2 ^ 59
def prefixEnd_647551 : Nat := 4983230072969 + 3 ^ 40 * 647551 * 2
def baseEnd_647551 : Nat := 49259986859214990731033

theorem tailTrace_647551 : CollatzResearch.WordTrace tailWord_647551 prefixEnd_647551 49259986859214990731033 := by
  unfold tailWord_647551
  simp only [CollatzResearch.WordTrace]
  refine ⟨23618125277040794751158507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15745416851360529834105671 23618125277040794751158507)
  ·
    refine ⟨35427187915561192126737761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23618125277040794751158507 35427187915561192126737761)
    ·
      refine ⟨26570390936670894095053321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35427187915561192126737761 26570390936670894095053321)
      ·
        refine ⟨19927793202503170571289991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26570390936670894095053321 19927793202503170571289991)
        ·
          refine ⟨29891689803754755856934987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19927793202503170571289991 29891689803754755856934987)
          ·
            refine ⟨44837534705632133785402481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29891689803754755856934987 44837534705632133785402481)
            ·
              refine ⟨33628151029224100339051861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44837534705632133785402481 33628151029224100339051861)
              ·
                refine ⟨49259986859214990731033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 33628151029224100339051861 49259986859214990731033)
                ·
                  rfl

theorem cell21_647551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 11].length) (baseStart_647551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647551 prefixEnd_647551 := by exact prefixLift 647551
  have htrace : WordTrace (prefixWord ++ tailWord_647551) baseStart_647551 baseEnd_647551 := by
    simpa [prefixWord, tailWord_647551, baseEnd_647551] using wordTrace_append hprefix tailTrace_647551
  have hstable : (prefixWord ++ tailWord_647551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647551).length < 2 ^ (prefixWord ++ tailWord_647551).sum := by decide
  have hdescent : baseEnd_647551 < baseStart_647551 := by decide
  rcases family_descends (prefixWord ++ tailWord_647551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647689 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 4]
def baseStart_647689 : Nat := 118140960795 + 647689 * 2 ^ 59
def prefixEnd_647689 : Nat := 4983230072969 + 3 ^ 40 * 647689 * 2
def baseEnd_647689 : Nat := 147811454057787398892817

theorem tailTrace_647689 : CollatzResearch.WordTrace tailWord_647689 prefixEnd_647689 147811454057787398892817 := by
  unfold tailWord_647689
  simp only [CollatzResearch.WordTrace]
  refine ⟨23623158550540844319682121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15748772367027229546454747 23623158550540844319682121)
  ·
    refine ⟨17717368912905633239761591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23623158550540844319682121 17717368912905633239761591)
    ·
      refine ⟨26576053369358449859642387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17717368912905633239761591 26576053369358449859642387)
      ·
        refine ⟨39864080054037674789463581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26576053369358449859642387 39864080054037674789463581)
        ·
          refine ⟨14949030020264128046048843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39864080054037674789463581 14949030020264128046048843)
          ·
            refine ⟨22423545030396192069073265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14949030020264128046048843 22423545030396192069073265)
            ·
              refine ⟨16817658772797144051804949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22423545030396192069073265 16817658772797144051804949)
              ·
                refine ⟨788327754974866127428357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16817658772797144051804949 788327754974866127428357)
                ·
                  refine ⟨147811454057787398892817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 788327754974866127428357 147811454057787398892817)
                  ·
                    rfl

theorem cell21_647689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_647689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647689 prefixEnd_647689 := by exact prefixLift 647689
  have htrace : WordTrace (prefixWord ++ tailWord_647689) baseStart_647689 baseEnd_647689 := by
    simpa [prefixWord, tailWord_647689, baseEnd_647689] using wordTrace_append hprefix tailTrace_647689
  have hstable : (prefixWord ++ tailWord_647689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647689).length < 2 ^ (prefixWord ++ tailWord_647689).sum := by decide
  have hdescent : baseEnd_647689 < baseStart_647689 := by decide
  rcases family_descends (prefixWord ++ tailWord_647689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647692 : List Nat := [2, 2, 1, 2, 4, 1, 2, 4, 3]
def baseStart_647692 : Nat := 118140960795 + 647692 * 2 ^ 59
def prefixEnd_647692 : Nat := 4983230072969 + 3 ^ 40 * 647692 * 2
def baseEnd_647692 : Nat := 147812138698660060342811

theorem tailTrace_647692 : CollatzResearch.WordTrace tailWord_647692 prefixEnd_647692 147812138698660060342811 := by
  unfold tailWord_647692
  simp only [CollatzResearch.WordTrace]
  refine ⟨11811633984764987916020665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15748845313019983888027553 11811633984764987916020665)
  ·
    refine ⟨8858725488573740937015499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11811633984764987916020665 8858725488573740937015499)
    ·
      refine ⟨13288088232860611405523249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8858725488573740937015499 13288088232860611405523249)
      ·
        refine ⟨9966066174645458554142437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13288088232860611405523249 9966066174645458554142437)
        ·
          refine ⟨1868637407746023478901707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9966066174645458554142437 1868637407746023478901707)
          ·
            refine ⟨2802956111619035218352561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868637407746023478901707 2802956111619035218352561)
            ·
              refine ⟨2102217083714276413764421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802956111619035218352561 2102217083714276413764421)
              ·
                refine ⟨394165703196426827580829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2102217083714276413764421 394165703196426827580829)
                ·
                  refine ⟨147812138698660060342811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394165703196426827580829 147812138698660060342811)
                  ·
                    rfl

theorem cell21_647692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_647692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647692 prefixEnd_647692 := by exact prefixLift 647692
  have htrace : WordTrace (prefixWord ++ tailWord_647692) baseStart_647692 baseEnd_647692 := by
    simpa [prefixWord, tailWord_647692, baseEnd_647692] using wordTrace_append hprefix tailTrace_647692
  have hstable : (prefixWord ++ tailWord_647692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647692).length < 2 ^ (prefixWord ++ tailWord_647692).sum := by decide
  have hdescent : baseEnd_647692 < baseStart_647692 := by decide
  rcases family_descends (prefixWord ++ tailWord_647692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647726 : List Nat := [4, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_647726 : Nat := 118140960795 + 647726 * 2 ^ 59
def prefixEnd_647726 : Nat := 4983230072969 + 3 ^ 40 * 647726 * 2
def baseEnd_647726 : Nat := 147819897961883556776075

theorem tailTrace_647726 : CollatzResearch.WordTrace tailWord_647726 prefixEnd_647726 147819897961883556776075 := by
  unfold tailWord_647726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2953063506425849954847379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15749672034271199759186021 2953063506425849954847379)
  ·
    refine ⟨4429595259638774932271069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2953063506425849954847379 4429595259638774932271069)
    ·
      refine ⟨1661098222364540599601651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4429595259638774932271069 1661098222364540599601651)
      ·
        refine ⟨2491647333546810899402477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661098222364540599601651 2491647333546810899402477)
        ·
          refine ⟨934367750080054087275929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2491647333546810899402477 934367750080054087275929)
          ·
            refine ⟨700775812560040565456947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 934367750080054087275929 700775812560040565456947)
            ·
              refine ⟨1051163718840060848185421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700775812560040565456947 1051163718840060848185421)
              ·
                refine ⟨394186394565022818069533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1051163718840060848185421 394186394565022818069533)
                ·
                  refine ⟨147819897961883556776075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394186394565022818069533 147819897961883556776075)
                  ·
                    rfl

theorem cell21_647726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_647726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647726 prefixEnd_647726 := by exact prefixLift 647726
  have htrace : WordTrace (prefixWord ++ tailWord_647726) baseStart_647726 baseEnd_647726 := by
    simpa [prefixWord, tailWord_647726, baseEnd_647726] using wordTrace_append hprefix tailTrace_647726
  have hstable : (prefixWord ++ tailWord_647726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647726).length < 2 ^ (prefixWord ++ tailWord_647726).sum := by decide
  have hdescent : baseEnd_647726 < baseStart_647726 := by decide
  rcases family_descends (prefixWord ++ tailWord_647726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647751 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 5]
def baseStart_647751 : Nat := 118140960795 + 647751 * 2 ^ 59
def prefixEnd_647751 : Nat := 4983230072969 + 3 ^ 40 * 647751 * 2
def baseEnd_647751 : Nat := 147825603302489068859357

theorem tailTrace_647751 : CollatzResearch.WordTrace tailWord_647751 prefixEnd_647751 147825603302489068859357 := by
  unfold tailWord_647751
  simp only [CollatzResearch.WordTrace]
  refine ⟨23625419876316228908439107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15750279917544152605626071 23625419876316228908439107)
  ·
    refine ⟨35438129814474343362658661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23625419876316228908439107 35438129814474343362658661)
    ·
      refine ⟨6644649340213939380498499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35438129814474343362658661 6644649340213939380498499)
      ·
        refine ⟨9966974010320909070747749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6644649340213939380498499 9966974010320909070747749)
        ·
          refine ⟨1868807626935170450765203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9966974010320909070747749 1868807626935170450765203)
          ·
            refine ⟨2803211440402755676147805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868807626935170450765203 2803211440402755676147805)
            ·
              refine ⟨1051204290151033378555427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2803211440402755676147805 1051204290151033378555427)
              ·
                refine ⟨1576806435226550067833141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051204290151033378555427 1576806435226550067833141)
                ·
                  refine ⟨147825603302489068859357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1576806435226550067833141 147825603302489068859357)
                  ·
                    rfl

theorem cell21_647751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 5].length) (baseStart_647751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647751 prefixEnd_647751 := by exact prefixLift 647751
  have htrace : WordTrace (prefixWord ++ tailWord_647751) baseStart_647751 baseEnd_647751 := by
    simpa [prefixWord, tailWord_647751, baseEnd_647751] using wordTrace_append hprefix tailTrace_647751
  have hstable : (prefixWord ++ tailWord_647751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647751).length < 2 ^ (prefixWord ++ tailWord_647751).sum := by decide
  have hdescent : baseEnd_647751 < baseStart_647751 := by decide
  rcases family_descends (prefixWord ++ tailWord_647751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647779 : List Nat := [1, 1, 1, 5, 1, 2, 1, 9]
def baseStart_647779 : Nat := 118140960795 + 647779 * 2 ^ 59
def prefixEnd_647779 : Nat := 4983230072969 + 3 ^ 40 * 647779 * 2
def baseEnd_647779 : Nat := 49277331094655747464211

theorem tailTrace_647779 : CollatzResearch.WordTrace tailWord_647779 prefixEnd_647779 49277331094655747464211 := by
  unfold tailWord_647779
  simp only [CollatzResearch.WordTrace]
  refine ⟨23626441120214789690458391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15750960746809859793638927 23626441120214789690458391)
  ·
    refine ⟨35439661680322184535687587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23626441120214789690458391 35439661680322184535687587)
    ·
      refine ⟨53159492520483276803531381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35439661680322184535687587 53159492520483276803531381)
      ·
        refine ⟨4983702423795307200331067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53159492520483276803531381 4983702423795307200331067)
        ·
          refine ⟨7475553635692960800496601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4983702423795307200331067 7475553635692960800496601)
          ·
            refine ⟨5606665226769720600372451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7475553635692960800496601 5606665226769720600372451)
            ·
              refine ⟨8409997840154580900558677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5606665226769720600372451 8409997840154580900558677)
              ·
                refine ⟨49277331094655747464211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8409997840154580900558677 49277331094655747464211)
                ·
                  rfl

theorem cell21_647779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 9].length) (baseStart_647779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647779 prefixEnd_647779 := by exact prefixLift 647779
  have htrace : WordTrace (prefixWord ++ tailWord_647779) baseStart_647779 baseEnd_647779 := by
    simpa [prefixWord, tailWord_647779, baseEnd_647779] using wordTrace_append hprefix tailTrace_647779
  have hstable : (prefixWord ++ tailWord_647779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647779).length < 2 ^ (prefixWord ++ tailWord_647779).sum := by decide
  have hdescent : baseEnd_647779 < baseStart_647779 := by decide
  rcases family_descends (prefixWord ++ tailWord_647779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647824 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_647824 : Nat := 118140960795 + 647824 * 2 ^ 59
def prefixEnd_647824 : Nat := 4983230072969 + 3 ^ 40 * 647824 * 2
def baseEnd_647824 : Nat := 147842262897057164142541

theorem tailTrace_647824 : CollatzResearch.WordTrace tailWord_647824 prefixEnd_647824 147842262897057164142541 := by
  unfold tailWord_647824
  simp only [CollatzResearch.WordTrace]
  refine ⟨11814041202525881187923263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15752054936701174917231017 11814041202525881187923263)
  ·
    refine ⟨17721061803788821781884895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11814041202525881187923263 17721061803788821781884895)
    ·
      refine ⟨26581592705683232672827343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17721061803788821781884895 26581592705683232672827343)
      ·
        refine ⟨39872389058524849009241015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26581592705683232672827343 39872389058524849009241015)
        ·
          refine ⟨59808583587787273513861523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39872389058524849009241015 59808583587787273513861523)
          ·
            refine ⟨89712875381680910270792285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59808583587787273513861523 89712875381680910270792285)
            ·
              refine ⟨33642328268130341351547107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89712875381680910270792285 33642328268130341351547107)
              ·
                refine ⟨50463492402195512027320661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33642328268130341351547107 50463492402195512027320661)
                ·
                  refine ⟨147842262897057164142541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 50463492402195512027320661 147842262897057164142541)
                  ·
                    rfl

theorem cell21_647824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_647824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647824 prefixEnd_647824 := by exact prefixLift 647824
  have htrace : WordTrace (prefixWord ++ tailWord_647824) baseStart_647824 baseEnd_647824 := by
    simpa [prefixWord, tailWord_647824, baseEnd_647824] using wordTrace_append hprefix tailTrace_647824
  have hstable : (prefixWord ++ tailWord_647824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647824).length < 2 ^ (prefixWord ++ tailWord_647824).sum := by decide
  have hdescent : baseEnd_647824 < baseStart_647824 := by decide
  rcases family_descends (prefixWord ++ tailWord_647824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647844 : List Nat := [2, 3, 1, 2, 2, 1, 4, 3, 3]
def baseStart_647844 : Nat := 118140960795 + 647844 * 2 ^ 59
def prefixEnd_647844 : Nat := 4983230072969 + 3 ^ 40 * 647844 * 2
def baseEnd_647844 : Nat := 147846827169541573809167

theorem tailTrace_647844 : CollatzResearch.WordTrace tailWord_647844 prefixEnd_647844 147846827169541573809167 := by
  unfold tailWord_647844
  simp only [CollatzResearch.WordTrace]
  refine ⟨11814405932489652895787293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15752541243319537194383057 11814405932489652895787293)
  ·
    refine ⟨4430402224683619835920235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11814405932489652895787293 4430402224683619835920235)
    ·
      refine ⟨6645603337025429753880353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4430402224683619835920235 6645603337025429753880353)
      ·
        refine ⟨4984202502769072315410265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6645603337025429753880353 4984202502769072315410265)
        ·
          refine ⟨3738151877076804236557699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4984202502769072315410265 3738151877076804236557699)
          ·
            refine ⟨5607227815615206354836549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3738151877076804236557699 5607227815615206354836549)
            ·
              refine ⟨1051355215427851191531853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5607227815615206354836549 1051355215427851191531853)
              ·
                refine ⟨394258205785444196824445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1051355215427851191531853 394258205785444196824445)
                ·
                  refine ⟨147846827169541573809167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394258205785444196824445 147846827169541573809167)
                  ·
                    rfl

theorem cell21_647844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_647844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647844 prefixEnd_647844 := by exact prefixLift 647844
  have htrace : WordTrace (prefixWord ++ tailWord_647844) baseStart_647844 baseEnd_647844 := by
    simpa [prefixWord, tailWord_647844, baseEnd_647844] using wordTrace_append hprefix tailTrace_647844
  have hstable : (prefixWord ++ tailWord_647844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647844).length < 2 ^ (prefixWord ++ tailWord_647844).sum := by decide
  have hdescent : baseEnd_647844 < baseStart_647844 := by decide
  rcases family_descends (prefixWord ++ tailWord_647844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647855 : List Nat := [1, 1, 2, 1, 2, 6, 8]
def baseStart_647855 : Nat := 118140960795 + 647855 * 2 ^ 59
def prefixEnd_647855 : Nat := 4983230072969 + 3 ^ 40 * 647855 * 2
def baseEnd_647855 : Nat := 16427704168823111013979

theorem tailTrace_647855 : CollatzResearch.WordTrace tailWord_647855 prefixEnd_647855 16427704168823111013979 := by
  unfold tailWord_647855
  simp only [CollatzResearch.WordTrace]
  refine ⟨23629213067939454670225019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15752808711959636446816679 23629213067939454670225019)
  ·
    refine ⟨35443819601909182005337529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23629213067939454670225019 35443819601909182005337529)
    ·
      refine ⟨26582864701431886504003147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35443819601909182005337529 26582864701431886504003147)
      ·
        refine ⟨39874297052147829756004721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26582864701431886504003147 39874297052147829756004721)
        ·
          refine ⟨29905722789110872317003541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39874297052147829756004721 29905722789110872317003541)
          ·
            refine ⟨1401830755739572139859541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29905722789110872317003541 1401830755739572139859541)
            ·
              refine ⟨16427704168823111013979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1401830755739572139859541 16427704168823111013979)
              ·
                rfl

theorem cell21_647855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 8].length) (baseStart_647855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647855 prefixEnd_647855 := by exact prefixLift 647855
  have htrace : WordTrace (prefixWord ++ tailWord_647855) baseStart_647855 baseEnd_647855 := by
    simpa [prefixWord, tailWord_647855, baseEnd_647855] using wordTrace_append hprefix tailTrace_647855
  have hstable : (prefixWord ++ tailWord_647855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647855).length < 2 ^ (prefixWord ++ tailWord_647855).sum := by decide
  have hdescent : baseEnd_647855 < baseStart_647855 := by decide
  rcases family_descends (prefixWord ++ tailWord_647855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647917 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 6]
def baseStart_647917 : Nat := 118140960795 + 647917 * 2 ^ 59
def prefixEnd_647917 : Nat := 4983230072969 + 3 ^ 40 * 647917 * 2
def baseEnd_647917 : Nat := 147863486764109669092351

theorem tailTrace_647917 : CollatzResearch.WordTrace tailWord_647917 prefixEnd_647917 147863486764109669092351 := by
  unfold tailWord_647917
  simp only [CollatzResearch.WordTrace]
  refine ⟨23631474393714839258982005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15754316262476559505988003 23631474393714839258982005)
  ·
    refine ⟨2215450724410766180529563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23631474393714839258982005 2215450724410766180529563)
    ·
      refine ⟨3323176086616149270794345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2215450724410766180529563 3323176086616149270794345)
      ·
        refine ⟨2492382064962111953095759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3323176086616149270794345 2492382064962111953095759)
        ·
          refine ⟨3738573097443167929643639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492382064962111953095759 3738573097443167929643639)
          ·
            refine ⟨5607859646164751894465459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3738573097443167929643639 5607859646164751894465459)
            ·
              refine ⟨8411789469247127841698189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5607859646164751894465459 8411789469247127841698189)
              ·
                refine ⟨3154421050967672940636821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8411789469247127841698189 3154421050967672940636821)
                ·
                  refine ⟨147863486764109669092351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3154421050967672940636821 147863486764109669092351)
                  ·
                    rfl

theorem cell21_647917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_647917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647917 prefixEnd_647917 := by exact prefixLift 647917
  have htrace : WordTrace (prefixWord ++ tailWord_647917) baseStart_647917 baseEnd_647917 := by
    simpa [prefixWord, tailWord_647917, baseEnd_647917] using wordTrace_append hprefix tailTrace_647917
  have hstable : (prefixWord ++ tailWord_647917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647917).length < 2 ^ (prefixWord ++ tailWord_647917).sum := by decide
  have hdescent : baseEnd_647917 < baseStart_647917 := by decide
  rcases family_descends (prefixWord ++ tailWord_647917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647920 : List Nat := [2, 1, 1, 1, 3, 1, 7, 2, 3]
def baseStart_647920 : Nat := 118140960795 + 647920 * 2 ^ 59
def prefixEnd_647920 : Nat := 4983230072969 + 3 ^ 40 * 647920 * 2
def baseEnd_647920 : Nat := 147864171404982330542345

theorem tailTrace_647920 : CollatzResearch.WordTrace tailWord_647920 prefixEnd_647920 147864171404982330542345 := by
  unfold tailWord_647920
  simp only [CollatzResearch.WordTrace]
  refine ⟨11815791906351985385670607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15754389208469313847560809 11815791906351985385670607)
  ·
    refine ⟨17723687859527978078505911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11815791906351985385670607 17723687859527978078505911)
    ·
      refine ⟨26585531789291967117758867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17723687859527978078505911 26585531789291967117758867)
      ·
        refine ⟨39878297683937950676638301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26585531789291967117758867 39878297683937950676638301)
        ·
          refine ⟨14954361631476731503739363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39878297683937950676638301 14954361631476731503739363)
          ·
            refine ⟨22431542447215097255609045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14954361631476731503739363 22431542447215097255609045)
            ·
              refine ⟨525739276106603841928337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 22431542447215097255609045 525739276106603841928337)
              ·
                refine ⟨394304457079952881446253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525739276106603841928337 394304457079952881446253)
                ·
                  refine ⟨147864171404982330542345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394304457079952881446253 147864171404982330542345)
                  ·
                    rfl

theorem cell21_647920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 3].length) (baseStart_647920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647920 prefixEnd_647920 := by exact prefixLift 647920
  have htrace : WordTrace (prefixWord ++ tailWord_647920) baseStart_647920 baseEnd_647920 := by
    simpa [prefixWord, tailWord_647920, baseEnd_647920] using wordTrace_append hprefix tailTrace_647920
  have hstable : (prefixWord ++ tailWord_647920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647920).length < 2 ^ (prefixWord ++ tailWord_647920).sum := by decide
  have hdescent : baseEnd_647920 < baseStart_647920 := by decide
  rcases family_descends (prefixWord ++ tailWord_647920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_647965 : List Nat := [1, 4, 2, 4, 2, 8]
def baseStart_647965 : Nat := 118140960795 + 647965 * 2 ^ 59
def prefixEnd_647965 : Nat := 4983230072969 + 3 ^ 40 * 647965 * 2
def baseEnd_647965 : Nat := 5476831148817490825639

theorem tailTrace_647965 : CollatzResearch.WordTrace tailWord_647965 prefixEnd_647965 5476831148817490825639 := by
  unfold tailWord_647965
  simp only [CollatzResearch.WordTrace]
  refine ⟨23633225097540943456729349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15755483398360628971152899 23633225097540943456729349)
  ·
    refine ⟨4431229705788926898136753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23633225097540943456729349 4431229705788926898136753)
    ·
      refine ⟨3323422279341695173602565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4431229705788926898136753 3323422279341695173602565)
      ·
        refine ⟨623141677376567845050481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3323422279341695173602565 623141677376567845050481)
        ·
          refine ⟨467356258032425883787861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623141677376567845050481 467356258032425883787861)
          ·
            refine ⟨5476831148817490825639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 467356258032425883787861 5476831148817490825639)
            ·
              rfl

theorem cell21_647965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 8].length) (baseStart_647965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_647965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_647965 prefixEnd_647965 := by exact prefixLift 647965
  have htrace : WordTrace (prefixWord ++ tailWord_647965) baseStart_647965 baseEnd_647965 := by
    simpa [prefixWord, tailWord_647965, baseEnd_647965] using wordTrace_append hprefix tailTrace_647965
  have hstable : (prefixWord ++ tailWord_647965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_647965).length < 2 ^ (prefixWord ++ tailWord_647965).sum := by decide
  have hdescent : baseEnd_647965 < baseStart_647965 := by decide
  rcases family_descends (prefixWord ++ tailWord_647965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648072 : List Nat := [2, 1, 3, 3, 2, 1, 3, 3, 3]
def baseStart_648072 : Nat := 118140960795 + 648072 * 2 ^ 59
def prefixEnd_648072 : Nat := 4983230072969 + 3 ^ 40 * 648072 * 2
def baseEnd_648072 : Nat := 147898859875863844008701

theorem tailTrace_648072 : CollatzResearch.WordTrace tailWord_648072 prefixEnd_648072 147898859875863844008701 := by
  unfold tailWord_648072
  simp only [CollatzResearch.WordTrace]
  refine ⟨11818563854076650365437235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15758085138768867153916313 11818563854076650365437235)
  ·
    refine ⟨17727845781114975548155853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11818563854076650365437235 17727845781114975548155853)
    ·
      refine ⟨6647942167918115830558445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17727845781114975548155853 6647942167918115830558445)
      ·
        refine ⟨2492978312969293436459417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6647942167918115830558445 2492978312969293436459417)
        ·
          refine ⟨1869733734726970077344563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2492978312969293436459417 1869733734726970077344563)
          ·
            refine ⟨2804600602090455116016845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869733734726970077344563 2804600602090455116016845)
            ·
              refine ⟨1051725225783920668506317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2804600602090455116016845 1051725225783920668506317)
              ·
                refine ⟨394396959668970250689869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1051725225783920668506317 394396959668970250689869)
                ·
                  refine ⟨147898859875863844008701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394396959668970250689869 147898859875863844008701)
                  ·
                    rfl

theorem cell21_648072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 3].length) (baseStart_648072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648072 prefixEnd_648072 := by exact prefixLift 648072
  have htrace : WordTrace (prefixWord ++ tailWord_648072) baseStart_648072 baseEnd_648072 := by
    simpa [prefixWord, tailWord_648072, baseEnd_648072] using wordTrace_append hprefix tailTrace_648072
  have hstable : (prefixWord ++ tailWord_648072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648072).length < 2 ^ (prefixWord ++ tailWord_648072).sum := by decide
  have hdescent : baseEnd_648072 < baseStart_648072 := by decide
  rcases family_descends (prefixWord ++ tailWord_648072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648134 : List Nat := [6, 1, 3, 1, 10]
def baseStart_648134 : Nat := 118140960795 + 648134 * 2 ^ 59
def prefixEnd_648134 : Nat := 4983230072969 + 3 ^ 40 * 648134 * 2
def baseEnd_648134 : Nat := 1826086532352660666361

theorem tailTrace_648134 : CollatzResearch.WordTrace tailWord_648134 prefixEnd_648134 1826086532352660666361 := by
  unfold tailWord_648134
  simp only [CollatzResearch.WordTrace]
  refine ⟨738730907310271416238483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15759592689285790213087637 738730907310271416238483)
  ·
    refine ⟨1108096360965407124357725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 738730907310271416238483 1108096360965407124357725)
    ·
      refine ⟨415536135362027671634147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1108096360965407124357725 415536135362027671634147)
      ·
        refine ⟨623304203043041507451221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415536135362027671634147 623304203043041507451221)
        ·
          refine ⟨1826086532352660666361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 623304203043041507451221 1826086532352660666361)
          ·
            rfl

theorem cell21_648134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 10].length) (baseStart_648134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648134 prefixEnd_648134 := by exact prefixLift 648134
  have htrace : WordTrace (prefixWord ++ tailWord_648134) baseStart_648134 baseEnd_648134 := by
    simpa [prefixWord, tailWord_648134, baseEnd_648134] using wordTrace_append hprefix tailTrace_648134
  have hstable : (prefixWord ++ tailWord_648134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648134).length < 2 ^ (prefixWord ++ tailWord_648134).sum := by decide
  have hdescent : baseEnd_648134 < baseStart_648134 := by decide
  rcases family_descends (prefixWord ++ tailWord_648134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648145 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 4]
def baseStart_648145 : Nat := 118140960795 + 648145 * 2 ^ 59
def prefixEnd_648145 : Nat := 4983230072969 + 3 ^ 40 * 648145 * 2
def baseEnd_648145 : Nat := 147915519470431939291885

theorem tailTrace_648145 : CollatzResearch.WordTrace tailWord_648145 prefixEnd_648145 147915519470431939291885 := by
  unfold tailWord_648145
  simp only [CollatzResearch.WordTrace]
  refine ⟨23639790236888834198281889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15759860157925889465521259 23639790236888834198281889)
  ·
    refine ⟨17729842677666625648711417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23639790236888834198281889 17729842677666625648711417)
    ·
      refine ⟨13297382008249969236533563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17729842677666625648711417 13297382008249969236533563)
      ·
        refine ⟨19946073012374953854800345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13297382008249969236533563 19946073012374953854800345)
        ·
          refine ⟨14959554759281215391100259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19946073012374953854800345 14959554759281215391100259)
          ·
            refine ⟨22439332138921823086650389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14959554759281215391100259 22439332138921823086650389)
            ·
              refine ⟨1051843694011960457186737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22439332138921823086650389 1051843694011960457186737)
              ·
                refine ⟨788882770508970342890053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051843694011960457186737 788882770508970342890053)
                ·
                  refine ⟨147915519470431939291885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 788882770508970342890053 147915519470431939291885)
                  ·
                    rfl

theorem cell21_648145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_648145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648145 prefixEnd_648145 := by exact prefixLift 648145
  have htrace : WordTrace (prefixWord ++ tailWord_648145) baseStart_648145 baseEnd_648145 := by
    simpa [prefixWord, tailWord_648145, baseEnd_648145] using wordTrace_append hprefix tailTrace_648145
  have hstable : (prefixWord ++ tailWord_648145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648145).length < 2 ^ (prefixWord ++ tailWord_648145).sum := by decide
  have hdescent : baseEnd_648145 < baseStart_648145 := by decide
  rcases family_descends (prefixWord ++ tailWord_648145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648148 : List Nat := [2, 4, 1, 2, 1, 3, 1, 4, 3]
def baseStart_648148 : Nat := 118140960795 + 648148 * 2 ^ 59
def prefixEnd_648148 : Nat := 4983230072969 + 3 ^ 40 * 648148 * 2
def baseEnd_648148 : Nat := 147916204111304600741879

theorem tailTrace_648148 : CollatzResearch.WordTrace tailWord_648148 prefixEnd_648148 147916204111304600741879 := by
  unfold tailWord_648148
  simp only [CollatzResearch.WordTrace]
  refine ⟨11819949827938982855320549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15759933103918643807094065 11819949827938982855320549)
  ·
    refine ⟨2216240592738559285372603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11819949827938982855320549 2216240592738559285372603)
    ·
      refine ⟨3324360889107838928058905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2216240592738559285372603 3324360889107838928058905)
      ·
        refine ⟨2493270666830879196044179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3324360889107838928058905 2493270666830879196044179)
        ·
          refine ⟨3739906000246318794066269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2493270666830879196044179 3739906000246318794066269)
          ·
            refine ⟨1402464750092369547774851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3739906000246318794066269 1402464750092369547774851)
            ·
              refine ⟨2103697125138554321662277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402464750092369547774851 2103697125138554321662277)
              ·
                refine ⟨394443210963478935311677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2103697125138554321662277 394443210963478935311677)
                ·
                  refine ⟨147916204111304600741879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394443210963478935311677 147916204111304600741879)
                  ·
                    rfl

theorem cell21_648148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_648148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648148 prefixEnd_648148 := by exact prefixLift 648148
  have htrace : WordTrace (prefixWord ++ tailWord_648148) baseStart_648148 baseEnd_648148 := by
    simpa [prefixWord, tailWord_648148, baseEnd_648148] using wordTrace_append hprefix tailTrace_648148
  have hstable : (prefixWord ++ tailWord_648148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648148).length < 2 ^ (prefixWord ++ tailWord_648148).sum := by decide
  have hdescent : baseEnd_648148 < baseStart_648148 := by decide
  rcases family_descends (prefixWord ++ tailWord_648148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648266 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_648266 : Nat := 118140960795 + 648266 * 2 ^ 59
def prefixEnd_648266 : Nat := 4983230072969 + 3 ^ 40 * 648266 * 2
def baseEnd_648266 : Nat := 147943133318962617774971

theorem tailTrace_648266 : CollatzResearch.WordTrace tailWord_648266 prefixEnd_648266 147943133318962617774971 := by
  unfold tailWord_648266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5911050867362617965859163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15762802312966981242291101 5911050867362617965859163)
  ·
    refine ⟨8866576301043926948788745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5911050867362617965859163 8866576301043926948788745)
    ·
      refine ⟨6649932225782945211591559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8866576301043926948788745 6649932225782945211591559)
      ·
        refine ⟨9974898338674417817387339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6649932225782945211591559 9974898338674417817387339)
        ·
          refine ⟨14962347508011626726081009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9974898338674417817387339 14962347508011626726081009)
          ·
            refine ⟨11221760631008720044560757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14962347508011626726081009 11221760631008720044560757)
            ·
              refine ⟨1052040059157067504177571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11221760631008720044560757 1052040059157067504177571)
              ·
                refine ⟨1578060088735601256266357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052040059157067504177571 1578060088735601256266357)
                ·
                  refine ⟨147943133318962617774971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1578060088735601256266357 147943133318962617774971)
                  ·
                    rfl

theorem cell21_648266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_648266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648266 prefixEnd_648266 := by exact prefixLift 648266
  have htrace : WordTrace (prefixWord ++ tailWord_648266) baseStart_648266 baseEnd_648266 := by
    simpa [prefixWord, tailWord_648266, baseEnd_648266] using wordTrace_append hprefix tailTrace_648266
  have hstable : (prefixWord ++ tailWord_648266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648266).length < 2 ^ (prefixWord ++ tailWord_648266).sum := by decide
  have hdescent : baseEnd_648266 < baseStart_648266 := by decide
  rcases family_descends (prefixWord ++ tailWord_648266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648449 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 4]
def baseStart_648449 : Nat := 118140960795 + 648449 * 2 ^ 59
def prefixEnd_648449 : Nat := 4983230072969 + 3 ^ 40 * 648449 * 2
def baseEnd_648449 : Nat := 147984896412194966224597

theorem tailTrace_648449 : CollatzResearch.WordTrace tailWord_648449 prefixEnd_648449 147984896412194966224597 := by
  unfold tailWord_648449
  simp only [CollatzResearch.WordTrace]
  refine ⟨23650878027787494117348401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15767252018524996078232267 23650878027787494117348401)
  ·
    refine ⟨17738158520840620588011301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23650878027787494117348401 17738158520840620588011301)
    ·
      refine ⟨3325904722657616360252119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17738158520840620588011301 3325904722657616360252119)
      ·
        refine ⟨4988857083986424540378179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325904722657616360252119 4988857083986424540378179)
        ·
          refine ⟨7483285625979636810567269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4988857083986424540378179 7483285625979636810567269)
          ·
            refine ⟨1403116054871181901981363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7483285625979636810567269 1403116054871181901981363)
            ·
              refine ⟨2104674082306772852972045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1403116054871181901981363 2104674082306772852972045)
              ·
                refine ⟨789252780865039819864517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2104674082306772852972045 789252780865039819864517)
                ·
                  refine ⟨147984896412194966224597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 789252780865039819864517 147984896412194966224597)
                  ·
                    rfl

theorem cell21_648449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_648449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648449 prefixEnd_648449 := by exact prefixLift 648449
  have htrace : WordTrace (prefixWord ++ tailWord_648449) baseStart_648449 baseEnd_648449 := by
    simpa [prefixWord, tailWord_648449, baseEnd_648449] using wordTrace_append hprefix tailTrace_648449
  have hstable : (prefixWord ++ tailWord_648449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648449).length < 2 ^ (prefixWord ++ tailWord_648449).sum := by decide
  have hdescent : baseEnd_648449 < baseStart_648449 := by decide
  rcases family_descends (prefixWord ++ tailWord_648449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648522 : List Nat := [3, 1, 2, 1, 1, 1, 1, 11]
def baseStart_648522 : Nat := 118140960795 + 648522 * 2 ^ 59
def prefixEnd_648522 : Nat := 4983230072969 + 3 ^ 40 * 648522 * 2
def baseEnd_648522 : Nat := 49333852002254353835927

theorem tailTrace_648522 : CollatzResearch.WordTrace tailWord_648522 prefixEnd_648522 49333852002254353835927 := by
  unfold tailWord_648522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5913385139130756896188955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15769027037682018389837213 5913385139130756896188955)
  ·
    refine ⟨8870077708696135344283433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5913385139130756896188955 8870077708696135344283433)
    ·
      refine ⟨6652558281522101508212575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8870077708696135344283433 6652558281522101508212575)
      ·
        refine ⟨9978837422283152262318863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6652558281522101508212575 9978837422283152262318863)
        ·
          refine ⟨14968256133424728393478295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9978837422283152262318863 14968256133424728393478295)
          ·
            refine ⟨22452384200137092590217443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14968256133424728393478295 22452384200137092590217443)
            ·
              refine ⟨33678576300205638885326165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22452384200137092590217443 33678576300205638885326165)
              ·
                refine ⟨49333852002254353835927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 33678576300205638885326165 49333852002254353835927)
                ·
                  rfl

theorem cell21_648522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_648522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648522 prefixEnd_648522 := by exact prefixLift 648522
  have htrace : WordTrace (prefixWord ++ tailWord_648522) baseStart_648522 baseEnd_648522 := by
    simpa [prefixWord, tailWord_648522, baseEnd_648522] using wordTrace_append hprefix tailTrace_648522
  have hstable : (prefixWord ++ tailWord_648522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648522).length < 2 ^ (prefixWord ++ tailWord_648522).sum := by decide
  have hdescent : baseEnd_648522 < baseStart_648522 := by decide
  rcases family_descends (prefixWord ++ tailWord_648522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648534 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_648534 : Nat := 118140960795 + 648534 * 2 ^ 59
def prefixEnd_648534 : Nat := 4983230072969 + 3 ^ 40 * 648534 * 2
def baseEnd_648534 : Nat := 148004294570253707307757

theorem tailTrace_648534 : CollatzResearch.WordTrace tailWord_648534 prefixEnd_648534 148004294570253707307757 := by
  unfold tailWord_648534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478373639529972102137041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15769318821653035756128437 1478373639529972102137041)
  ·
    refine ⟨1108780229647479076602781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1478373639529972102137041 1108780229647479076602781)
    ·
      refine ⟨415792586117804653726043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1108780229647479076602781 415792586117804653726043)
      ·
        refine ⟨623688879176706980589065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415792586117804653726043 623688879176706980589065)
        ·
          refine ⟨467766659382530235441799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623688879176706980589065 467766659382530235441799)
          ·
            refine ⟨701649989073795353162699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467766659382530235441799 701649989073795353162699)
            ·
              refine ⟨1052474983610693029744049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701649989073795353162699 1052474983610693029744049)
              ·
                refine ⟨789356237708019772308037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052474983610693029744049 789356237708019772308037)
                ·
                  refine ⟨148004294570253707307757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 789356237708019772308037 148004294570253707307757)
                  ·
                    rfl

theorem cell21_648534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_648534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648534 prefixEnd_648534 := by exact prefixLift 648534
  have htrace : WordTrace (prefixWord ++ tailWord_648534) baseStart_648534 baseEnd_648534 := by
    simpa [prefixWord, tailWord_648534, baseEnd_648534] using wordTrace_append hprefix tailTrace_648534
  have hstable : (prefixWord ++ tailWord_648534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648534).length < 2 ^ (prefixWord ++ tailWord_648534).sum := by decide
  have hdescent : baseEnd_648534 < baseStart_648534 := by decide
  rcases family_descends (prefixWord ++ tailWord_648534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648584 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_648584 : Nat := 118140960795 + 648584 * 2 ^ 59
def prefixEnd_648584 : Nat := 4983230072969 + 3 ^ 40 * 648584 * 2
def baseEnd_648584 : Nat := 148015705251464731474321

theorem tailTrace_648584 : CollatzResearch.WordTrace tailWord_648584 prefixEnd_648584 148015705251464731474321 := by
  unfold tailWord_648584
  simp only [CollatzResearch.WordTrace]
  refine ⟨11827900941149206086756403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15770534588198941449008537 11827900941149206086756403)
  ·
    refine ⟨17741851411723809130134605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11827900941149206086756403 17741851411723809130134605)
    ·
      refine ⟨6653194279396428423800477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17741851411723809130134605 6653194279396428423800477)
      ·
        refine ⟨2494947854773660658925179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6653194279396428423800477 2494947854773660658925179)
        ·
          refine ⟨3742421782160490988387769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2494947854773660658925179 3742421782160490988387769)
          ·
            refine ⟨2806816336620368241290827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3742421782160490988387769 2806816336620368241290827)
            ·
              refine ⟨4210224504930552361936241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806816336620368241290827 4210224504930552361936241)
              ·
                refine ⟨3157668378697914271452181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4210224504930552361936241 3157668378697914271452181)
                ·
                  refine ⟨148015705251464731474321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3157668378697914271452181 148015705251464731474321)
                  ·
                    rfl

theorem cell21_648584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_648584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648584 prefixEnd_648584 := by exact prefixLift 648584
  have htrace : WordTrace (prefixWord ++ tailWord_648584) baseStart_648584 baseEnd_648584 := by
    simpa [prefixWord, tailWord_648584, baseEnd_648584] using wordTrace_append hprefix tailTrace_648584
  have hstable : (prefixWord ++ tailWord_648584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648584).length < 2 ^ (prefixWord ++ tailWord_648584).sum := by decide
  have hdescent : baseEnd_648584 < baseStart_648584 := by decide
  rcases family_descends (prefixWord ++ tailWord_648584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648604 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 5]
def baseStart_648604 : Nat := 118140960795 + 648604 * 2 ^ 59
def prefixEnd_648604 : Nat := 4983230072969 + 3 ^ 40 * 648604 * 2
def baseEnd_648604 : Nat := 148020269523949141140947

theorem tailTrace_648604 : CollatzResearch.WordTrace tailWord_648604 prefixEnd_648604 148020269523949141140947 := by
  unfold tailWord_648604
  simp only [CollatzResearch.WordTrace]
  refine ⟨11828265671112977794620433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15771020894817303726160577 11828265671112977794620433)
  ·
    refine ⟨8871199253334733345965325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11828265671112977794620433 8871199253334733345965325)
    ·
      refine ⟨3326699720000525004736997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8871199253334733345965325 3326699720000525004736997)
      ·
        refine ⟨623756197500098438388187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3326699720000525004736997 623756197500098438388187)
        ·
          refine ⟨935634296250147657582281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623756197500098438388187 935634296250147657582281)
          ·
            refine ⟨701725722187610743186711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 935634296250147657582281 701725722187610743186711)
            ·
              refine ⟨1052588583281416114780067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701725722187610743186711 1052588583281416114780067)
              ·
                refine ⟨1578882874922124172170101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052588583281416114780067 1578882874922124172170101)
                ·
                  refine ⟨148020269523949141140947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1578882874922124172170101 148020269523949141140947)
                  ·
                    rfl

theorem cell21_648604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_648604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648604 prefixEnd_648604 := by exact prefixLift 648604
  have htrace : WordTrace (prefixWord ++ tailWord_648604) baseStart_648604 baseEnd_648604 := by
    simpa [prefixWord, tailWord_648604, baseEnd_648604] using wordTrace_append hprefix tailTrace_648604
  have hstable : (prefixWord ++ tailWord_648604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648604).length < 2 ^ (prefixWord ++ tailWord_648604).sum := by decide
  have hdescent : baseEnd_648604 < baseStart_648604 := by decide
  rcases family_descends (prefixWord ++ tailWord_648604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648615 : List Nat := [1, 1, 6, 1, 1, 1, 4, 6]
def baseStart_648615 : Nat := 118140960795 + 648615 * 2 ^ 59
def prefixEnd_648615 : Nat := 4983230072969 + 3 ^ 40 * 648615 * 2
def baseEnd_648615 : Nat := 49340926624605188819197

theorem tailTrace_648615 : CollatzResearch.WordTrace tailWord_648615 prefixEnd_648615 49340926624605188819197 := by
  unfold tailWord_648615
  simp only [CollatzResearch.WordTrace]
  refine ⟨23656932545186104467891299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15771288363457402978594199 23656932545186104467891299)
  ·
    refine ⟨35485398817779156701836949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23656932545186104467891299 35485398817779156701836949)
    ·
      refine ⟨1663378069583397970398607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35485398817779156701836949 1663378069583397970398607)
      ·
        refine ⟨2495067104375096955597911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663378069583397970398607 2495067104375096955597911)
        ·
          refine ⟨3742600656562645433396867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495067104375096955597911 3742600656562645433396867)
          ·
            refine ⟨5613900984843968150095301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3742600656562645433396867 5613900984843968150095301)
            ·
              refine ⟨1052606434658244028142869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5613900984843968150095301 1052606434658244028142869)
              ·
                refine ⟨49340926624605188819197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1052606434658244028142869 49340926624605188819197)
                ·
                  rfl

theorem cell21_648615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 6].length) (baseStart_648615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648615 prefixEnd_648615 := by exact prefixLift 648615
  have htrace : WordTrace (prefixWord ++ tailWord_648615) baseStart_648615 baseEnd_648615 := by
    simpa [prefixWord, tailWord_648615, baseEnd_648615] using wordTrace_append hprefix tailTrace_648615
  have hstable : (prefixWord ++ tailWord_648615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648615).length < 2 ^ (prefixWord ++ tailWord_648615).sum := by decide
  have hdescent : baseEnd_648615 < baseStart_648615 := by decide
  rcases family_descends (prefixWord ++ tailWord_648615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648643 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 8]
def baseStart_648643 : Nat := 118140960795 + 648643 * 2 ^ 59
def prefixEnd_648643 : Nat := 4983230072969 + 3 ^ 40 * 648643 * 2
def baseEnd_648643 : Nat := 148029169855293739990867

theorem tailTrace_648643 : CollatzResearch.WordTrace tailWord_648643 prefixEnd_648643 148029169855293739990867 := by
  unfold tailWord_648643
  simp only [CollatzResearch.WordTrace]
  refine ⟨23657953789084665249910583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15771969192723110166607055 23657953789084665249910583)
  ·
    refine ⟨35486930683626997874865875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23657953789084665249910583 35486930683626997874865875)
    ·
      refine ⟨53230396025440496812298813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35486930683626997874865875 53230396025440496812298813)
      ·
        refine ⟨19961398509540186304612055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53230396025440496812298813 19961398509540186304612055)
        ·
          refine ⟨29942097764310279456918083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19961398509540186304612055 29942097764310279456918083)
          ·
            refine ⟨44913146646465419185377125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29942097764310279456918083 44913146646465419185377125)
            ·
              refine ⟨8421214996212266097258211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44913146646465419185377125 8421214996212266097258211)
              ·
                refine ⟨12631822494318399145887317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8421214996212266097258211 12631822494318399145887317)
                ·
                  refine ⟨148029169855293739990867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12631822494318399145887317 148029169855293739990867)
                  ·
                    rfl

theorem cell21_648643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_648643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648643 prefixEnd_648643 := by exact prefixLift 648643
  have htrace : WordTrace (prefixWord ++ tailWord_648643) baseStart_648643 baseEnd_648643 := by
    simpa [prefixWord, tailWord_648643, baseEnd_648643] using wordTrace_append hprefix tailTrace_648643
  have hstable : (prefixWord ++ tailWord_648643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648643).length < 2 ^ (prefixWord ++ tailWord_648643).sum := by decide
  have hdescent : baseEnd_648643 < baseStart_648643 := by decide
  rcases family_descends (prefixWord ++ tailWord_648643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648677 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 4]
def baseStart_648677 : Nat := 118140960795 + 648677 * 2 ^ 59
def prefixEnd_648677 : Nat := 4983230072969 + 3 ^ 40 * 648677 * 2
def baseEnd_648677 : Nat := 148036929118517236424131

theorem tailTrace_648677 : CollatzResearch.WordTrace tailWord_648677 prefixEnd_648677 148036929118517236424131 := by
  unfold tailWord_648677
  simp only [CollatzResearch.WordTrace]
  refine ⟨23659193870961489056648285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15772795913974326037765523 23659193870961489056648285)
  ·
    refine ⟨8872197701610558396243107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23659193870961489056648285 8872197701610558396243107)
    ·
      refine ⟨13308296552415837594364661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8872197701610558396243107 13308296552415837594364661)
      ·
        refine ⟨1247652801788984774471687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13308296552415837594364661 1247652801788984774471687)
        ·
          refine ⟨1871479202683477161707531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1247652801788984774471687 1871479202683477161707531)
          ·
            refine ⟨2807218804025215742561297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871479202683477161707531 2807218804025215742561297)
            ·
              refine ⟨2105414103018911806920973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2807218804025215742561297 2105414103018911806920973)
              ·
                refine ⟨789530288632091927595365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2105414103018911806920973 789530288632091927595365)
                ·
                  refine ⟨148036929118517236424131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 789530288632091927595365 148036929118517236424131)
                  ·
                    rfl

theorem cell21_648677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_648677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648677 prefixEnd_648677 := by exact prefixLift 648677
  have htrace : WordTrace (prefixWord ++ tailWord_648677) baseStart_648677 baseEnd_648677 := by
    simpa [prefixWord, tailWord_648677, baseEnd_648677] using wordTrace_append hprefix tailTrace_648677
  have hstable : (prefixWord ++ tailWord_648677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648677).length < 2 ^ (prefixWord ++ tailWord_648677).sum := by decide
  have hdescent : baseEnd_648677 < baseStart_648677 := by decide
  rcases family_descends (prefixWord ++ tailWord_648677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648829 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 4]
def baseStart_648829 : Nat := 118140960795 + 648829 * 2 ^ 59
def prefixEnd_648829 : Nat := 4983230072969 + 3 ^ 40 * 648829 * 2
def baseEnd_648829 : Nat := 148071617589398749890487

theorem tailTrace_648829 : CollatzResearch.WordTrace tailWord_648829 prefixEnd_648829 148071617589398749890487 := by
  unfold tailWord_648829
  simp only [CollatzResearch.WordTrace]
  refine ⟨23664737766410819016181541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15776491844273879344121027 23664737766410819016181541)
  ·
    refine ⟨4437138331202028565534039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23664737766410819016181541 4437138331202028565534039)
    ·
      refine ⟨6655707496803042848301059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4437138331202028565534039 6655707496803042848301059)
      ·
        refine ⟨9983561245204564272451589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6655707496803042848301059 9983561245204564272451589)
        ·
          refine ⟨1871917733475855801084673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9983561245204564272451589 1871917733475855801084673)
          ·
            refine ⟨1403938300106891850813505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1871917733475855801084673 1403938300106891850813505)
            ·
              refine ⟨1052953725080168888110129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403938300106891850813505 1052953725080168888110129)
              ·
                refine ⟨789715293810126666082597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052953725080168888110129 789715293810126666082597)
                ·
                  refine ⟨148071617589398749890487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 789715293810126666082597 148071617589398749890487)
                  ·
                    rfl

theorem cell21_648829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_648829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648829 prefixEnd_648829 := by exact prefixLift 648829
  have htrace : WordTrace (prefixWord ++ tailWord_648829) baseStart_648829 baseEnd_648829 := by
    simpa [prefixWord, tailWord_648829, baseEnd_648829] using wordTrace_append hprefix tailTrace_648829
  have hstable : (prefixWord ++ tailWord_648829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648829).length < 2 ^ (prefixWord ++ tailWord_648829).sum := by decide
  have hdescent : baseEnd_648829 < baseStart_648829 := by decide
  rcases family_descends (prefixWord ++ tailWord_648829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648860 : List Nat := [2, 2, 3, 2, 3, 1, 3, 5]
def baseStart_648860 : Nat := 118140960795 + 648860 * 2 ^ 59
def prefixEnd_648860 : Nat := 4983230072969 + 3 ^ 40 * 648860 * 2
def baseEnd_648860 : Nat := 49359564070583194957919

theorem tailTrace_648860 : CollatzResearch.WordTrace tailWord_648860 prefixEnd_648860 49359564070583194957919 := by
  unfold tailWord_648860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11832934214649255655280017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15777245619532340873706689 11832934214649255655280017)
  ·
    refine ⟨8874700660986941741460013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11832934214649255655280017 8874700660986941741460013)
    ·
      refine ⟨3328012747870103153047505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8874700660986941741460013 3328012747870103153047505)
      ·
        refine ⟨2496009560902577364785629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3328012747870103153047505 2496009560902577364785629)
        ·
          refine ⟨936003585338466511794611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2496009560902577364785629 936003585338466511794611)
          ·
            refine ⟨1404005378007699767691917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936003585338466511794611 1404005378007699767691917)
            ·
              refine ⟨526502016752887412884469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1404005378007699767691917 526502016752887412884469)
              ·
                refine ⟨49359564070583194957919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 526502016752887412884469 49359564070583194957919)
                ·
                  rfl

theorem cell21_648860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_648860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648860 prefixEnd_648860 := by exact prefixLift 648860
  have htrace : WordTrace (prefixWord ++ tailWord_648860) baseStart_648860 baseEnd_648860 := by
    simpa [prefixWord, tailWord_648860, baseEnd_648860] using wordTrace_append hprefix tailTrace_648860
  have hstable : (prefixWord ++ tailWord_648860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648860).length < 2 ^ (prefixWord ++ tailWord_648860).sum := by decide
  have hdescent : baseEnd_648860 < baseStart_648860 := by decide
  rcases family_descends (prefixWord ++ tailWord_648860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648925 : List Nat := [1, 4, 3, 3, 1, 2, 1, 3, 3]
def baseStart_648925 : Nat := 118140960795 + 648925 * 2 ^ 59
def prefixEnd_648925 : Nat := 4983230072969 + 3 ^ 40 * 648925 * 2
def baseEnd_648925 : Nat := 148093526097323916290291

theorem tailTrace_648925 : CollatzResearch.WordTrace tailWord_648925 prefixEnd_648925 148093526097323916290291 := by
  unfold tailWord_648925
  simp only [CollatzResearch.WordTrace]
  refine ⟨23668239174063027411676229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15778826116042018274450819 23668239174063027411676229)
  ·
    refine ⟨4437794845136817639689293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23668239174063027411676229 4437794845136817639689293)
    ·
      refine ⟨1664173066926306614883485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4437794845136817639689293 1664173066926306614883485)
      ·
        refine ⟨624064900097364980581307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1664173066926306614883485 624064900097364980581307)
        ·
          refine ⟨936097350146047470871961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624064900097364980581307 936097350146047470871961)
          ·
            refine ⟨702073012609535603153971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 936097350146047470871961 702073012609535603153971)
            ·
              refine ⟨1053109518914303404730957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702073012609535603153971 1053109518914303404730957)
              ·
                refine ⟨394916069592863776774109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1053109518914303404730957 394916069592863776774109)
                ·
                  refine ⟨148093526097323916290291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394916069592863776774109 148093526097323916290291)
                  ·
                    rfl

theorem cell21_648925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_648925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648925 prefixEnd_648925 := by exact prefixLift 648925
  have htrace : WordTrace (prefixWord ++ tailWord_648925) baseStart_648925 baseEnd_648925 := by
    simpa [prefixWord, tailWord_648925, baseEnd_648925] using wordTrace_append hprefix tailTrace_648925
  have hstable : (prefixWord ++ tailWord_648925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648925).length < 2 ^ (prefixWord ++ tailWord_648925).sum := by decide
  have hdescent : baseEnd_648925 < baseStart_648925 := by decide
  rcases family_descends (prefixWord ++ tailWord_648925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648947 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 6]
def baseStart_648947 : Nat := 118140960795 + 648947 * 2 ^ 59
def prefixEnd_648947 : Nat := 4983230072969 + 3 ^ 40 * 648947 * 2
def baseEnd_648947 : Nat := 148098546797056766923579

theorem tailTrace_648947 : CollatzResearch.WordTrace tailWord_648947 prefixEnd_648947 148098546797056766923579 := by
  unfold tailWord_648947
  simp only [CollatzResearch.WordTrace]
  refine ⟨23669041579983325168977095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15779361053322216779318063 23669041579983325168977095)
  ·
    refine ⟨35503562369974987753465643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23669041579983325168977095 35503562369974987753465643)
    ·
      refine ⟨53255343554962481630198465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35503562369974987753465643 53255343554962481630198465)
      ·
        refine ⟨39941507666221861222648849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53255343554962481630198465 39941507666221861222648849)
        ·
          refine ⟨29956130749666395916986637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39941507666221861222648849 29956130749666395916986637)
          ·
            refine ⟨11233549031124898468869989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29956130749666395916986637 11233549031124898468869989)
            ·
              refine ⟨2106290443335918462913123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11233549031124898468869989 2106290443335918462913123)
              ·
                refine ⟨3159435665003877694369685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106290443335918462913123 3159435665003877694369685)
                ·
                  refine ⟨148098546797056766923579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3159435665003877694369685 148098546797056766923579)
                  ·
                    rfl

theorem cell21_648947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_648947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648947 prefixEnd_648947 := by exact prefixLift 648947
  have htrace : WordTrace (prefixWord ++ tailWord_648947) baseStart_648947 baseEnd_648947 := by
    simpa [prefixWord, tailWord_648947, baseEnd_648947] using wordTrace_append hprefix tailTrace_648947
  have hstable : (prefixWord ++ tailWord_648947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648947).length < 2 ^ (prefixWord ++ tailWord_648947).sum := by decide
  have hdescent : baseEnd_648947 < baseStart_648947 := by decide
  rcases family_descends (prefixWord ++ tailWord_648947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648950 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_648950 : Nat := 118140960795 + 648950 * 2 ^ 59
def prefixEnd_648950 : Nat := 4983230072969 + 3 ^ 40 * 648950 * 2
def baseEnd_648950 : Nat := 148099231437929428373573

theorem tailTrace_648950 : CollatzResearch.WordTrace tailWord_648950 prefixEnd_648950 148099231437929428373573 := by
  unfold tailWord_648950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479321937435778542583519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15779433999314971120890869 1479321937435778542583519)
  ·
    refine ⟨2218982906153667813875279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1479321937435778542583519 2218982906153667813875279)
    ·
      refine ⟨3328474359230501720812919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2218982906153667813875279 3328474359230501720812919)
      ·
        refine ⟨4992711538845752581219379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3328474359230501720812919 4992711538845752581219379)
        ·
          refine ⟨7489067308268628871829069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4992711538845752581219379 7489067308268628871829069)
          ·
            refine ⟨2808400240600735826935901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7489067308268628871829069 2808400240600735826935901)
            ·
              refine ⟨1053150090225275935100963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2808400240600735826935901 1053150090225275935100963)
              ·
                refine ⟨1579725135337913902651445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053150090225275935100963 1579725135337913902651445)
                ·
                  refine ⟨148099231437929428373573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1579725135337913902651445 148099231437929428373573)
                  ·
                    rfl

theorem cell21_648950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_648950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_648950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_648950 prefixEnd_648950 := by exact prefixLift 648950
  have htrace : WordTrace (prefixWord ++ tailWord_648950) baseStart_648950 baseEnd_648950 := by
    simpa [prefixWord, tailWord_648950, baseEnd_648950] using wordTrace_append hprefix tailTrace_648950
  have hstable : (prefixWord ++ tailWord_648950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648950).length < 2 ^ (prefixWord ++ tailWord_648950).sum := by decide
  have hdescent : baseEnd_648950 < baseStart_648950 := by decide
  rcases family_descends (prefixWord ++ tailWord_648950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649012 : List Nat := [2, 5, 1, 1, 2, 3, 1, 6]
def baseStart_649012 : Nat := 118140960795 + 649012 * 2 ^ 59
def prefixEnd_649012 : Nat := 4983230072969 + 3 ^ 40 * 649012 * 2
def baseEnd_649012 : Nat := 49371126894210366113371

theorem tailTrace_649012 : CollatzResearch.WordTrace tailWord_649012 prefixEnd_649012 49371126894210366113371 := by
  unfold tailWord_649012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11835706162373920635046645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15780941549831894180062193 11835706162373920635046645)
  ·
    refine ⟨1109597452722555059535623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11835706162373920635046645 1109597452722555059535623)
    ·
      refine ⟨1664396179083832589303435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109597452722555059535623 1664396179083832589303435)
      ·
        refine ⟨2496594268625748883955153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1664396179083832589303435 2496594268625748883955153)
        ·
          refine ⟨1872445701469311662966365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2496594268625748883955153 1872445701469311662966365)
          ·
            refine ⟨702167138050991873612387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1872445701469311662966365 702167138050991873612387)
            ·
              refine ⟨1053250707076487810418581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702167138050991873612387 1053250707076487810418581)
              ·
                refine ⟨49371126894210366113371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1053250707076487810418581 49371126894210366113371)
                ·
                  rfl

theorem cell21_649012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_649012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649012 prefixEnd_649012 := by exact prefixLift 649012
  have htrace : WordTrace (prefixWord ++ tailWord_649012) baseStart_649012 baseEnd_649012 := by
    simpa [prefixWord, tailWord_649012, baseEnd_649012] using wordTrace_append hprefix tailTrace_649012
  have hstable : (prefixWord ++ tailWord_649012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649012).length < 2 ^ (prefixWord ++ tailWord_649012).sum := by decide
  have hdescent : baseEnd_649012 < baseStart_649012 := by decide
  rcases family_descends (prefixWord ++ tailWord_649012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649113 : List Nat := [1, 2, 1, 2, 1, 3, 11]
def baseStart_649113 : Nat := 118140960795 + 649113 * 2 ^ 59
def prefixEnd_649113 : Nat := 4983230072969 + 3 ^ 40 * 649113 * 2
def baseEnd_649113 : Nat := 16459603362075263017397

theorem tailTrace_649113 : CollatzResearch.WordTrace tailWord_649113 prefixEnd_649113 16459603362075263017397 := by
  unfold tailWord_649113
  simp only [CollatzResearch.WordTrace]
  refine ⟨23675096097381935519519993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15783397398254623679679995 23675096097381935519519993)
  ·
    refine ⟨17756322073036451639639995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23675096097381935519519993 17756322073036451639639995)
    ·
      refine ⟨26634483109554677459459993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17756322073036451639639995 26634483109554677459459993)
      ·
        refine ⟨19975862332166008094594995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26634483109554677459459993 19975862332166008094594995)
        ·
          refine ⟨29963793498249012141892493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19975862332166008094594995 29963793498249012141892493)
          ·
            refine ⟨11236422561843379553209685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29963793498249012141892493 11236422561843379553209685)
            ·
              refine ⟨16459603362075263017397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11236422561843379553209685 16459603362075263017397)
              ·
                rfl

theorem cell21_649113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 11].length) (baseStart_649113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649113 prefixEnd_649113 := by exact prefixLift 649113
  have htrace : WordTrace (prefixWord ++ tailWord_649113) baseStart_649113 baseEnd_649113 := by
    simpa [prefixWord, tailWord_649113, baseEnd_649113] using wordTrace_append hprefix tailTrace_649113
  have hstable : (prefixWord ++ tailWord_649113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649113).length < 2 ^ (prefixWord ++ tailWord_649113).sum := by decide
  have hdescent : baseEnd_649113 < baseStart_649113 := by decide
  rcases family_descends (prefixWord ++ tailWord_649113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649116 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 6]
def baseStart_649116 : Nat := 118140960795 + 649116 * 2 ^ 59
def prefixEnd_649116 : Nat := 4983230072969 + 3 ^ 40 * 649116 * 2
def baseEnd_649116 : Nat := 148137114899550028606567

theorem tailTrace_649116 : CollatzResearch.WordTrace tailWord_649116 prefixEnd_649116 148137114899550028606567 := by
  unfold tailWord_649116
  simp only [CollatzResearch.WordTrace]
  refine ⟨11837602758185533515939601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15783470344247378021252801 11837602758185533515939601)
  ·
    refine ⟨8878202068639150136954701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11837602758185533515939601 8878202068639150136954701)
    ·
      refine ⟨3329325775739681301358013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8878202068639150136954701 3329325775739681301358013)
      ·
        refine ⟨1248497165902380488009255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3329325775739681301358013 1248497165902380488009255)
        ·
          refine ⟨1872745748853570732013883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248497165902380488009255 1872745748853570732013883)
          ·
            refine ⟨2809118623280356098020825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872745748853570732013883 2809118623280356098020825)
            ·
              refine ⟨2106838967460267073515619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2809118623280356098020825 2106838967460267073515619)
              ·
                refine ⟨3160258451190400610273429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106838967460267073515619 3160258451190400610273429)
                ·
                  refine ⟨148137114899550028606567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3160258451190400610273429 148137114899550028606567)
                  ·
                    rfl

theorem cell21_649116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_649116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649116 prefixEnd_649116 := by exact prefixLift 649116
  have htrace : WordTrace (prefixWord ++ tailWord_649116) baseStart_649116 baseEnd_649116 := by
    simpa [prefixWord, tailWord_649116, baseEnd_649116] using wordTrace_append hprefix tailTrace_649116
  have hstable : (prefixWord ++ tailWord_649116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649116).length < 2 ^ (prefixWord ++ tailWord_649116).sum := by decide
  have hdescent : baseEnd_649116 < baseStart_649116 := by decide
  rcases family_descends (prefixWord ++ tailWord_649116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649119 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 5]
def baseStart_649119 : Nat := 118140960795 + 649119 * 2 ^ 59
def prefixEnd_649119 : Nat := 4983230072969 + 3 ^ 40 * 649119 * 2
def baseEnd_649119 : Nat := 148137799540422690056561

theorem tailTrace_649119 : CollatzResearch.WordTrace tailWord_649119 prefixEnd_649119 148137799540422690056561 := by
  unfold tailWord_649119
  simp only [CollatzResearch.WordTrace]
  refine ⟨23675314935360198544238411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15783543290240132362825607 23675314935360198544238411)
  ·
    refine ⟨35512972403040297816357617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23675314935360198544238411 35512972403040297816357617)
    ·
      refine ⟨26634729302280223362268213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35512972403040297816357617 26634729302280223362268213)
      ·
        refine ⟨2497005872088770940212645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26634729302280223362268213 2497005872088770940212645)
        ·
          refine ⟨468188601016644551289871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2497005872088770940212645 468188601016644551289871)
          ·
            refine ⟨702282901524966826934807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468188601016644551289871 702282901524966826934807)
            ·
              refine ⟨1053424352287450240402211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702282901524966826934807 1053424352287450240402211)
              ·
                refine ⟨1580136528431175360603317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053424352287450240402211 1580136528431175360603317)
                ·
                  refine ⟨148137799540422690056561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1580136528431175360603317 148137799540422690056561)
                  ·
                    rfl

theorem cell21_649119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 5].length) (baseStart_649119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649119 prefixEnd_649119 := by exact prefixLift 649119
  have htrace : WordTrace (prefixWord ++ tailWord_649119) baseStart_649119 baseEnd_649119 := by
    simpa [prefixWord, tailWord_649119, baseEnd_649119] using wordTrace_append hprefix tailTrace_649119
  have hstable : (prefixWord ++ tailWord_649119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649119).length < 2 ^ (prefixWord ++ tailWord_649119).sum := by decide
  have hdescent : baseEnd_649119 < baseStart_649119 := by decide
  rcases family_descends (prefixWord ++ tailWord_649119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649144 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_649144 : Nat := 118140960795 + 649144 * 2 ^ 59
def prefixEnd_649144 : Nat := 4983230072969 + 3 ^ 40 * 649144 * 2
def baseEnd_649144 : Nat := 148143504881028202139843

theorem tailTrace_649144 : CollatzResearch.WordTrace tailWord_649144 prefixEnd_649144 148143504881028202139843 := by
  unfold tailWord_649144
  simp only [CollatzResearch.WordTrace]
  refine ⟨11838113380134813906949243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15784151173513085209265657 11838113380134813906949243)
  ·
    refine ⟨17757170070202220860423865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11838113380134813906949243 17757170070202220860423865)
    ·
      refine ⟨13317877552651665645317899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17757170070202220860423865 13317877552651665645317899)
      ·
        refine ⟨19976816328977498467976849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13317877552651665645317899 19976816328977498467976849)
        ·
          refine ⟨14982612246733123850982637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19976816328977498467976849 14982612246733123850982637)
          ·
            refine ⟨5618479592524921444118489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14982612246733123850982637 5618479592524921444118489)
            ·
              refine ⟨4213859694393691083088867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5618479592524921444118489 4213859694393691083088867)
              ·
                refine ⟨6320789541590536624633301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4213859694393691083088867 6320789541590536624633301)
                ·
                  refine ⟨148143504881028202139843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6320789541590536624633301 148143504881028202139843)
                  ·
                    rfl

theorem cell21_649144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_649144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649144 prefixEnd_649144 := by exact prefixLift 649144
  have htrace : WordTrace (prefixWord ++ tailWord_649144) baseStart_649144 baseEnd_649144 := by
    simpa [prefixWord, tailWord_649144, baseEnd_649144] using wordTrace_append hprefix tailTrace_649144
  have hstable : (prefixWord ++ tailWord_649144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649144).length < 2 ^ (prefixWord ++ tailWord_649144).sum := by decide
  have hdescent : baseEnd_649144 < baseStart_649144 := by decide
  rcases family_descends (prefixWord ++ tailWord_649144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649226 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 4]
def baseStart_649226 : Nat := 118140960795 + 649226 * 2 ^ 59
def prefixEnd_649226 : Nat := 4983230072969 + 3 ^ 40 * 649226 * 2
def baseEnd_649226 : Nat := 148162218398214281773009

theorem tailTrace_649226 : CollatzResearch.WordTrace tailWord_649226 prefixEnd_649226 148162218398214281773009 := by
  unfold tailWord_649226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5919804386493138954595883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15786145030648370545589021 5919804386493138954595883)
  ·
    refine ⟨8879706579739708431893825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5919804386493138954595883 8879706579739708431893825)
    ·
      refine ⟨6659779934804781323920369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8879706579739708431893825 6659779934804781323920369)
      ·
        refine ⟨4994834951103585992940277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6659779934804781323920369 4994834951103585992940277)
        ·
          refine ⟨468265776665961186838151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4994834951103585992940277 468265776665961186838151)
          ·
            refine ⟨702398664998941780257227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468265776665961186838151 702398664998941780257227)
            ·
              refine ⟨1053597997498412670385841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702398664998941780257227 1053597997498412670385841)
              ·
                refine ⟨790198498123809502789381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053597997498412670385841 790198498123809502789381)
                ·
                  refine ⟨148162218398214281773009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 790198498123809502789381 148162218398214281773009)
                  ·
                    rfl

theorem cell21_649226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_649226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649226 prefixEnd_649226 := by exact prefixLift 649226
  have htrace : WordTrace (prefixWord ++ tailWord_649226) baseStart_649226 baseEnd_649226 := by
    simpa [prefixWord, tailWord_649226, baseEnd_649226] using wordTrace_append hprefix tailTrace_649226
  have hstable : (prefixWord ++ tailWord_649226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649226).length < 2 ^ (prefixWord ++ tailWord_649226).sum := by decide
  have hdescent : baseEnd_649226 < baseStart_649226 := by decide
  rcases family_descends (prefixWord ++ tailWord_649226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649302 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_649302 : Nat := 118140960795 + 649302 * 2 ^ 59
def prefixEnd_649302 : Nat := 4983230072969 + 3 ^ 40 * 649302 * 2
def baseEnd_649302 : Nat := 148179562633655038506187

theorem tailTrace_649302 : CollatzResearch.WordTrace tailWord_649302 prefixEnd_649302 148179562633655038506187 := by
  unfold tailWord_649302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1480124343356076299884385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15787992995798147198766773 1480124343356076299884385)
  ·
    refine ⟨1110093257517057224913289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1480124343356076299884385 1110093257517057224913289)
    ·
      refine ⟨832569943137792918684967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1110093257517057224913289 832569943137792918684967)
      ·
        refine ⟨1248854914706689378027451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832569943137792918684967 1248854914706689378027451)
        ·
          refine ⟨1873282372060034067041177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248854914706689378027451 1873282372060034067041177)
          ·
            refine ⟨1404961779045025550280883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1873282372060034067041177 1404961779045025550280883)
            ·
              refine ⟨2107442668567538325421325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404961779045025550280883 2107442668567538325421325)
              ·
                refine ⟨790291000712826872032997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2107442668567538325421325 790291000712826872032997)
                ·
                  refine ⟨148179562633655038506187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 790291000712826872032997 148179562633655038506187)
                  ·
                    rfl

theorem cell21_649302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_649302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649302 prefixEnd_649302 := by exact prefixLift 649302
  have htrace : WordTrace (prefixWord ++ tailWord_649302) baseStart_649302 baseEnd_649302 := by
    simpa [prefixWord, tailWord_649302, baseEnd_649302] using wordTrace_append hprefix tailTrace_649302
  have hstable : (prefixWord ++ tailWord_649302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649302).length < 2 ^ (prefixWord ++ tailWord_649302).sum := by decide
  have hdescent : baseEnd_649302 < baseStart_649302 := by decide
  rcases family_descends (prefixWord ++ tailWord_649302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649341 : List Nat := [1, 4, 1, 1, 3, 11]
def baseStart_649341 : Nat := 118140960795 + 649341 * 2 ^ 59
def prefixEnd_649341 : Nat := 4983230072969 + 3 ^ 40 * 649341 * 2
def baseEnd_649341 : Nat := 5488461591296282865041

theorem tailTrace_649341 : CollatzResearch.WordTrace tailWord_649341 prefixEnd_649341 5488461591296282865041 := by
  unfold tailWord_649341
  simp only [CollatzResearch.WordTrace]
  refine ⟨23683411940555930458819877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15788941293703953639213251 23683411940555930458819877)
  ·
    refine ⟨4440639738854236961028727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23683411940555930458819877 4440639738854236961028727)
    ·
      refine ⟨6660959608281355441543091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4440639738854236961028727 6660959608281355441543091)
      ·
        refine ⟨9991439412422033162314637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6660959608281355441543091 9991439412422033162314637)
        ·
          refine ⟨3746789779658262435867989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9991439412422033162314637 3746789779658262435867989)
          ·
            refine ⟨5488461591296282865041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3746789779658262435867989 5488461591296282865041)
            ·
              rfl

theorem cell21_649341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 11].length) (baseStart_649341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649341 prefixEnd_649341 := by exact prefixLift 649341
  have htrace : WordTrace (prefixWord ++ tailWord_649341) baseStart_649341 baseEnd_649341 := by
    simpa [prefixWord, tailWord_649341, baseEnd_649341] using wordTrace_append hprefix tailTrace_649341
  have hstable : (prefixWord ++ tailWord_649341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649341).length < 2 ^ (prefixWord ++ tailWord_649341).sum := by decide
  have hdescent : baseEnd_649341 < baseStart_649341 := by decide
  rcases family_descends (prefixWord ++ tailWord_649341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649347 : List Nat := [1, 1, 1, 3, 3, 5, 2, 2, 3]
def baseStart_649347 : Nat := 118140960795 + 649347 * 2 ^ 59
def prefixEnd_649347 : Nat := 4983230072969 + 3 ^ 40 * 649347 * 2
def baseEnd_649347 : Nat := 148189832246744960256095

theorem tailTrace_649347 : CollatzResearch.WordTrace tailWord_649347 prefixEnd_649347 148189832246744960256095 := by
  unfold tailWord_649347
  simp only [CollatzResearch.WordTrace]
  refine ⟨23683630778534193483538295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15789087185689462322358863 23683630778534193483538295)
  ·
    refine ⟨35525446167801290225307443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23683630778534193483538295 35525446167801290225307443)
    ·
      refine ⟨53288169251701935337961165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35525446167801290225307443 53288169251701935337961165)
      ·
        refine ⟨19983063469388225751735437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53288169251701935337961165 19983063469388225751735437)
        ·
          refine ⟨7493648801020584656900789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19983063469388225751735437 7493648801020584656900789)
          ·
            refine ⟨702529575095679811584449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7493648801020584656900789 702529575095679811584449)
            ·
              refine ⟨526897181321759858688337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702529575095679811584449 526897181321759858688337)
              ·
                refine ⟨395172885991319894016253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526897181321759858688337 395172885991319894016253)
                ·
                  refine ⟨148189832246744960256095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395172885991319894016253 148189832246744960256095)
                  ·
                    rfl

theorem cell21_649347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 3].length) (baseStart_649347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649347 prefixEnd_649347 := by exact prefixLift 649347
  have htrace : WordTrace (prefixWord ++ tailWord_649347) baseStart_649347 baseEnd_649347 := by
    simpa [prefixWord, tailWord_649347, baseEnd_649347] using wordTrace_append hprefix tailTrace_649347
  have hstable : (prefixWord ++ tailWord_649347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649347).length < 2 ^ (prefixWord ++ tailWord_649347).sum := by decide
  have hdescent : baseEnd_649347 < baseStart_649347 := by decide
  rcases family_descends (prefixWord ++ tailWord_649347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649375 : List Nat := [1, 1, 2, 6, 1, 2, 3, 5]
def baseStart_649375 : Nat := 118140960795 + 649375 * 2 ^ 59
def prefixEnd_649375 : Nat := 4983230072969 + 3 ^ 40 * 649375 * 2
def baseEnd_649375 : Nat := 49398740742741044596457

theorem tailTrace_649375 : CollatzResearch.WordTrace tailWord_649375 prefixEnd_649375 49398740742741044596457 := by
  unfold tailWord_649375
  simp only [CollatzResearch.WordTrace]
  refine ⟨23684652022432754265557579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15789768014955169510371719 23684652022432754265557579)
  ·
    refine ⟨35526978033649131398336369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23684652022432754265557579 35526978033649131398336369)
    ·
      refine ⟨26645233525236848548752277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35526978033649131398336369 26645233525236848548752277)
      ·
        refine ⟨1248995321495477275722763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26645233525236848548752277 1248995321495477275722763)
        ·
          refine ⟨1873492982243215913584145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248995321495477275722763 1873492982243215913584145)
          ·
            refine ⟨1405119736682411935188109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1873492982243215913584145 1405119736682411935188109)
            ·
              refine ⟨526919901255904475695541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1405119736682411935188109 526919901255904475695541)
              ·
                refine ⟨49398740742741044596457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 526919901255904475695541 49398740742741044596457)
                ·
                  rfl

theorem cell21_649375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 5].length) (baseStart_649375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649375 prefixEnd_649375 := by exact prefixLift 649375
  have htrace : WordTrace (prefixWord ++ tailWord_649375) baseStart_649375 baseEnd_649375 := by
    simpa [prefixWord, tailWord_649375, baseEnd_649375] using wordTrace_append hprefix tailTrace_649375
  have hstable : (prefixWord ++ tailWord_649375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649375).length < 2 ^ (prefixWord ++ tailWord_649375).sum := by decide
  have hdescent : baseEnd_649375 < baseStart_649375 := by decide
  rcases family_descends (prefixWord ++ tailWord_649375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649406 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_649406 : Nat := 118140960795 + 649406 * 2 ^ 59
def prefixEnd_649406 : Nat := 4983230072969 + 3 ^ 40 * 649406 * 2
def baseEnd_649406 : Nat := 148203296850573968772641

theorem tailTrace_649406 : CollatzResearch.WordTrace tailWord_649406 prefixEnd_649406 148203296850573968772641 := by
  unfold tailWord_649406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2960722835665055819992009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15790521790213631039957381 2960722835665055819992009)
  ·
    refine ⟨2220542126748791864994007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2960722835665055819992009 2220542126748791864994007)
    ·
      refine ⟨3330813190123187797491011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2220542126748791864994007 3330813190123187797491011)
      ·
        refine ⟨4996219785184781696236517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3330813190123187797491011 4996219785184781696236517)
        ·
          refine ⟨936791209722146568044347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4996219785184781696236517 936791209722146568044347)
          ·
            refine ⟨1405186814583219852066521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936791209722146568044347 1405186814583219852066521)
            ·
              refine ⟨1053890110937414889049891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405186814583219852066521 1053890110937414889049891)
              ·
                refine ⟨1580835166406122333574837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053890110937414889049891 1580835166406122333574837)
                ·
                  refine ⟨148203296850573968772641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1580835166406122333574837 148203296850573968772641)
                  ·
                    rfl

theorem cell21_649406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_649406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649406 prefixEnd_649406 := by exact prefixLift 649406
  have htrace : WordTrace (prefixWord ++ tailWord_649406) baseStart_649406 baseEnd_649406 := by
    simpa [prefixWord, tailWord_649406, baseEnd_649406] using wordTrace_append hprefix tailTrace_649406
  have hstable : (prefixWord ++ tailWord_649406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649406).length < 2 ^ (prefixWord ++ tailWord_649406).sum := by decide
  have hdescent : baseEnd_649406 < baseStart_649406 := by decide
  rcases family_descends (prefixWord ++ tailWord_649406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649434 : List Nat := [3, 1, 1, 2, 2, 1, 6, 5]
def baseStart_649434 : Nat := 118140960795 + 649434 * 2 ^ 59
def prefixEnd_649434 : Nat := 4983230072969 + 3 ^ 40 * 649434 * 2
def baseEnd_649434 : Nat := 49403228944017380768639

theorem tailTrace_649434 : CollatzResearch.WordTrace tailWord_649434 prefixEnd_649434 49403228944017380768639 := by
  unfold tailWord_649434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921700982304751835488839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15791202619479338227970237 5921700982304751835488839)
  ·
    refine ⟨8882551473457127753233259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5921700982304751835488839 8882551473457127753233259)
    ·
      refine ⟨13323827210185691629849889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8882551473457127753233259 13323827210185691629849889)
      ·
        refine ⟨9992870407639268722387417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13323827210185691629849889 9992870407639268722387417)
        ·
          refine ⟨7494652805729451541790563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9992870407639268722387417 7494652805729451541790563)
          ·
            refine ⟨11241979208594177312685845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7494652805729451541790563 11241979208594177312685845)
            ·
              refine ⟨526967775402852061532149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11241979208594177312685845 526967775402852061532149)
              ·
                refine ⟨49403228944017380768639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 526967775402852061532149 49403228944017380768639)
                ·
                  rfl

theorem cell21_649434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_649434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649434 prefixEnd_649434 := by exact prefixLift 649434
  have htrace : WordTrace (prefixWord ++ tailWord_649434) baseStart_649434 baseEnd_649434 := by
    simpa [prefixWord, tailWord_649434, baseEnd_649434] using wordTrace_append hprefix tailTrace_649434
  have hstable : (prefixWord ++ tailWord_649434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649434).length < 2 ^ (prefixWord ++ tailWord_649434).sum := by decide
  have hdescent : baseEnd_649434 < baseStart_649434 := by decide
  rcases family_descends (prefixWord ++ tailWord_649434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649493 : List Nat := [1, 3, 2, 1, 2, 1, 4, 7]
def baseStart_649493 : Nat := 118140960795 + 649493 * 2 ^ 59
def prefixEnd_649493 : Nat := 4983230072969 + 3 ^ 40 * 649493 * 2
def baseEnd_649493 : Nat := 49407717145293716940821

theorem tailTrace_649493 : CollatzResearch.WordTrace tailWord_649493 prefixEnd_649493 49407717145293716940821 := by
  unfold tailWord_649493
  simp only [CollatzResearch.WordTrace]
  refine ⟨23688955836005260418353133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15792637224003506945568755 23688955836005260418353133)
  ·
    refine ⟨8883358438501972656882425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23688955836005260418353133 8883358438501972656882425)
    ·
      refine ⟨6662518828876479492661819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8883358438501972656882425 6662518828876479492661819)
      ·
        refine ⟨9993778243314719238992729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6662518828876479492661819 9993778243314719238992729)
        ·
          refine ⟨7495333682486039429244547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9993778243314719238992729 7495333682486039429244547)
          ·
            refine ⟨11243000523729059143866821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7495333682486039429244547 11243000523729059143866821)
            ·
              refine ⟨2108062598199198589475029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11243000523729059143866821 2108062598199198589475029)
              ·
                refine ⟨49407717145293716940821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2108062598199198589475029 49407717145293716940821)
                ·
                  rfl

theorem cell21_649493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 7].length) (baseStart_649493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649493 prefixEnd_649493 := by exact prefixLift 649493
  have htrace : WordTrace (prefixWord ++ tailWord_649493) baseStart_649493 baseEnd_649493 := by
    simpa [prefixWord, tailWord_649493, baseEnd_649493] using wordTrace_append hprefix tailTrace_649493
  have hstable : (prefixWord ++ tailWord_649493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649493).length < 2 ^ (prefixWord ++ tailWord_649493).sum := by decide
  have hdescent : baseEnd_649493 < baseStart_649493 := by decide
  rcases family_descends (prefixWord ++ tailWord_649493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649589 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 4]
def baseStart_649589 : Nat := 118140960795 + 649589 * 2 ^ 59
def prefixEnd_649589 : Nat := 4983230072969 + 3 ^ 40 * 649589 * 2
def baseEnd_649589 : Nat := 148245059943806317222267

theorem tailTrace_649589 : CollatzResearch.WordTrace tailWord_649589 prefixEnd_649589 148245059943806317222267 := by
  unfold tailWord_649589
  simp only [CollatzResearch.WordTrace]
  refine ⟨23692457243657468813847821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15794971495771645875898547 23692457243657468813847821)
  ·
    refine ⟨8884671466371550805192933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23692457243657468813847821 8884671466371550805192933)
    ·
      refine ⟨1665875899944665775973675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8884671466371550805192933 1665875899944665775973675)
      ·
        refine ⟨2498813849916998663960513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1665875899944665775973675 2498813849916998663960513)
        ·
          refine ⟨1874110387437748997970385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2498813849916998663960513 1874110387437748997970385)
          ·
            refine ⟨1405582790578311748477789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1874110387437748997970385 1405582790578311748477789)
            ·
              refine ⟨527093546466866905679171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1405582790578311748477789 527093546466866905679171)
              ·
                refine ⟨790640319700300358518757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527093546466866905679171 790640319700300358518757)
                ·
                  refine ⟨148245059943806317222267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 790640319700300358518757 148245059943806317222267)
                  ·
                    rfl

theorem cell21_649589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_649589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649589 prefixEnd_649589 := by exact prefixLift 649589
  have htrace : WordTrace (prefixWord ++ tailWord_649589) baseStart_649589 baseEnd_649589 := by
    simpa [prefixWord, tailWord_649589, baseEnd_649589] using wordTrace_append hprefix tailTrace_649589
  have hstable : (prefixWord ++ tailWord_649589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649589).length < 2 ^ (prefixWord ++ tailWord_649589).sum := by decide
  have hdescent : baseEnd_649589 < baseStart_649589 := by decide
  rcases family_descends (prefixWord ++ tailWord_649589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649603 : List Nat := [1, 1, 1, 3, 6, 2, 2, 5]
def baseStart_649603 : Nat := 118140960795 + 649603 * 2 ^ 59
def prefixEnd_649603 : Nat := 4983230072969 + 3 ^ 40 * 649603 * 2
def baseEnd_649603 : Nat := 49416084978181801329635

theorem tailTrace_649603 : CollatzResearch.WordTrace tailWord_649603 prefixEnd_649603 49416084978181801329635 := by
  unfold tailWord_649603
  simp only [CollatzResearch.WordTrace]
  refine ⟨23692967865606749204857463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15795311910404499469904975 23692967865606749204857463)
  ·
    refine ⟨35539451798410123807286195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23692967865606749204857463 35539451798410123807286195)
    ·
      refine ⟨53309177697615185710929293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35539451798410123807286195 53309177697615185710929293)
      ·
        refine ⟨19990941636605694641598485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53309177697615185710929293 19990941636605694641598485)
        ·
          refine ⟨937075389215891936324929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19990941636605694641598485 937075389215891936324929)
          ·
            refine ⟨702806541911918952243697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 937075389215891936324929 702806541911918952243697)
            ·
              refine ⟨527104906433939214182773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702806541911918952243697 527104906433939214182773)
              ·
                refine ⟨49416084978181801329635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 527104906433939214182773 49416084978181801329635)
                ·
                  rfl

theorem cell21_649603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 5].length) (baseStart_649603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649603 prefixEnd_649603 := by exact prefixLift 649603
  have htrace : WordTrace (prefixWord ++ tailWord_649603) baseStart_649603 baseEnd_649603 := by
    simpa [prefixWord, tailWord_649603, baseEnd_649603] using wordTrace_append hprefix tailTrace_649603
  have hstable : (prefixWord ++ tailWord_649603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649603).length < 2 ^ (prefixWord ++ tailWord_649603).sum := by decide
  have hdescent : baseEnd_649603 < baseStart_649603 := by decide
  rcases family_descends (prefixWord ++ tailWord_649603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649631 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 4]
def baseStart_649631 : Nat := 118140960795 + 649631 * 2 ^ 59
def prefixEnd_649631 : Nat := 4983230072969 + 3 ^ 40 * 649631 * 2
def baseEnd_649631 : Nat := 148254644916023577522181

theorem tailTrace_649631 : CollatzResearch.WordTrace tailWord_649631 prefixEnd_649631 148254644916023577522181 := by
  unfold tailWord_649631
  simp only [CollatzResearch.WordTrace]
  refine ⟨23693989109505309986876747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15795992739670206657917831 23693989109505309986876747)
  ·
    refine ⟨35540983664257964980315121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23693989109505309986876747 35540983664257964980315121)
    ·
      refine ⟨26655737748193473735236341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35540983664257964980315121 26655737748193473735236341)
      ·
        refine ⟨2498975413893138162678407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26655737748193473735236341 2498975413893138162678407)
        ·
          refine ⟨3748463120839707244017611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498975413893138162678407 3748463120839707244017611)
          ·
            refine ⟨5622694681259560866026417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3748463120839707244017611 5622694681259560866026417)
            ·
              refine ⟨4217021010944670649519813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5622694681259560866026417 4217021010944670649519813)
              ·
                refine ⟨790691439552125746784965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4217021010944670649519813 790691439552125746784965)
                ·
                  refine ⟨148254644916023577522181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 790691439552125746784965 148254644916023577522181)
                  ·
                    rfl

theorem cell21_649631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 4].length) (baseStart_649631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649631 prefixEnd_649631 := by exact prefixLift 649631
  have htrace : WordTrace (prefixWord ++ tailWord_649631) baseStart_649631 baseEnd_649631 := by
    simpa [prefixWord, tailWord_649631, baseEnd_649631] using wordTrace_append hprefix tailTrace_649631
  have hstable : (prefixWord ++ tailWord_649631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649631).length < 2 ^ (prefixWord ++ tailWord_649631).sum := by decide
  have hdescent : baseEnd_649631 < baseStart_649631 := by decide
  rcases family_descends (prefixWord ++ tailWord_649631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649741 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 6]
def baseStart_649741 : Nat := 118140960795 + 649741 * 2 ^ 59
def prefixEnd_649741 : Nat := 4983230072969 + 3 ^ 40 * 649741 * 2
def baseEnd_649741 : Nat := 148279748414687830688623

theorem tailTrace_649741 : CollatzResearch.WordTrace tailWord_649741 prefixEnd_649741 148279748414687830688623 := by
  unfold tailWord_649741
  simp only [CollatzResearch.WordTrace]
  refine ⟨23698001139106798773381077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15798667426071199182254051 23698001139106798773381077)
  ·
    refine ⟨555421901697815596251119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23698001139106798773381077 555421901697815596251119)
    ·
      refine ⟨833132852546723394376679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555421901697815596251119 833132852546723394376679)
      ·
        refine ⟨1249699278820085091565019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833132852546723394376679 1249699278820085091565019)
        ·
          refine ⟨1874548918230127637347529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249699278820085091565019 1874548918230127637347529)
          ·
            refine ⟨1405911688672595728010647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1874548918230127637347529 1405911688672595728010647)
            ·
              refine ⟨2108867533008893592015971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405911688672595728010647 2108867533008893592015971)
              ·
                refine ⟨3163301299513340388023957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108867533008893592015971 3163301299513340388023957)
                ·
                  refine ⟨148279748414687830688623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3163301299513340388023957 148279748414687830688623)
                  ·
                    rfl

theorem cell21_649741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_649741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649741 prefixEnd_649741 := by exact prefixLift 649741
  have htrace : WordTrace (prefixWord ++ tailWord_649741) baseStart_649741 baseEnd_649741 := by
    simpa [prefixWord, tailWord_649741, baseEnd_649741] using wordTrace_append hprefix tailTrace_649741
  have hstable : (prefixWord ++ tailWord_649741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649741).length < 2 ^ (prefixWord ++ tailWord_649741).sum := by decide
  have hdescent : baseEnd_649741 < baseStart_649741 := by decide
  rcases family_descends (prefixWord ++ tailWord_649741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649752 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_649752 : Nat := 118140960795 + 649752 * 2 ^ 59
def prefixEnd_649752 : Nat := 4983230072969 + 3 ^ 40 * 649752 * 2
def baseEnd_649752 : Nat := 148282258764554256005267

theorem tailTrace_649752 : CollatzResearch.WordTrace tailWord_649752 prefixEnd_649752 148282258764554256005267 := by
  unfold tailWord_649752
  simp only [CollatzResearch.WordTrace]
  refine ⟨11849201171033473826015755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15798934894711298434687673 11849201171033473826015755)
  ·
    refine ⟨17773801756550210739023633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11849201171033473826015755 17773801756550210739023633)
    ·
      refine ⟨13330351317412658054267725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17773801756550210739023633 13330351317412658054267725)
      ·
        refine ⟨4998881744029746770350397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13330351317412658054267725 4998881744029746770350397)
        ·
          refine ⟨1874580654011155038881399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4998881744029746770350397 1874580654011155038881399)
          ·
            refine ⟨2811870981016732558322099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874580654011155038881399 2811870981016732558322099)
            ·
              refine ⟨4217806471525098837483149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811870981016732558322099 4217806471525098837483149)
              ·
                refine ⟨1581677426821912064056181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4217806471525098837483149 1581677426821912064056181)
                ·
                  refine ⟨148282258764554256005267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1581677426821912064056181 148282258764554256005267)
                  ·
                    rfl

theorem cell21_649752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_649752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649752 prefixEnd_649752 := by exact prefixLift 649752
  have htrace : WordTrace (prefixWord ++ tailWord_649752) baseStart_649752 baseEnd_649752 := by
    simpa [prefixWord, tailWord_649752, baseEnd_649752] using wordTrace_append hprefix tailTrace_649752
  have hstable : (prefixWord ++ tailWord_649752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649752).length < 2 ^ (prefixWord ++ tailWord_649752).sum := by decide
  have hdescent : baseEnd_649752 < baseStart_649752 := by decide
  rcases family_descends (prefixWord ++ tailWord_649752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649786 : List Nat := [3, 1, 1, 1, 3, 5, 1, 3, 3]
def baseStart_649786 : Nat := 118140960795 + 649786 * 2 ^ 59
def prefixEnd_649786 : Nat := 4983230072969 + 3 ^ 40 * 649786 * 2
def baseEnd_649786 : Nat := 148290018027777752438531

theorem tailTrace_649786 : CollatzResearch.WordTrace tailWord_649786 prefixEnd_649786 148290018027777752438531 := by
  unfold tailWord_649786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5924910605985942864692303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15799761615962514305846141 5924910605985942864692303)
  ·
    refine ⟨8887365908978914297038455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5924910605985942864692303 8887365908978914297038455)
    ·
      refine ⟨13331048863468371445557683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8887365908978914297038455 13331048863468371445557683)
      ·
        refine ⟨19996573295202557168336525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13331048863468371445557683 19996573295202557168336525)
        ·
          refine ⟨7498714985700958938126197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19996573295202557168336525 7498714985700958938126197)
          ·
            refine ⟨703004529909464900449331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7498714985700958938126197 703004529909464900449331)
            ·
              refine ⟨1054506794864197350673997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703004529909464900449331 1054506794864197350673997)
              ·
                refine ⟨395440048074074006502749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1054506794864197350673997 395440048074074006502749)
                ·
                  refine ⟨148290018027777752438531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395440048074074006502749 148290018027777752438531)
                  ·
                    rfl

theorem cell21_649786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_649786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649786 prefixEnd_649786 := by exact prefixLift 649786
  have htrace : WordTrace (prefixWord ++ tailWord_649786) baseStart_649786 baseEnd_649786 := by
    simpa [prefixWord, tailWord_649786, baseEnd_649786] using wordTrace_append hprefix tailTrace_649786
  have hstable : (prefixWord ++ tailWord_649786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649786).length < 2 ^ (prefixWord ++ tailWord_649786).sum := by decide
  have hdescent : baseEnd_649786 < baseStart_649786 := by decide
  rcases family_descends (prefixWord ++ tailWord_649786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649797 : List Nat := [1, 3, 1, 1, 1, 7, 7]
def baseStart_649797 : Nat := 118140960795 + 649797 * 2 ^ 59
def prefixEnd_649797 : Nat := 4983230072969 + 3 ^ 40 * 649797 * 2
def baseEnd_649797 : Nat := 16476947597516019750575

theorem tailTrace_649797 : CollatzResearch.WordTrace tailWord_649797 prefixEnd_649797 16476947597516019750575 := by
  unfold tailWord_649797
  simp only [CollatzResearch.WordTrace]
  refine ⟨23700043626903920337419645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15800029084602613558279763 23700043626903920337419645)
  ·
    refine ⟨8887516360088970126532367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23700043626903920337419645 8887516360088970126532367)
    ·
      refine ⟨13331274540133455189798551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8887516360088970126532367 13331274540133455189798551)
      ·
        refine ⟨19996911810200182784697827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13331274540133455189798551 19996911810200182784697827)
        ·
          refine ⟨29995367715300274177046741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19996911810200182784697827 29995367715300274177046741)
          ·
            refine ⟨703016430827350176024533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29995367715300274177046741 703016430827350176024533)
            ·
              refine ⟨16476947597516019750575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 703016430827350176024533 16476947597516019750575)
              ·
                rfl

theorem cell21_649797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 7].length) (baseStart_649797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649797 prefixEnd_649797 := by exact prefixLift 649797
  have htrace : WordTrace (prefixWord ++ tailWord_649797) baseStart_649797 baseEnd_649797 := by
    simpa [prefixWord, tailWord_649797, baseEnd_649797] using wordTrace_append hprefix tailTrace_649797
  have hstable : (prefixWord ++ tailWord_649797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649797).length < 2 ^ (prefixWord ++ tailWord_649797).sum := by decide
  have hdescent : baseEnd_649797 < baseStart_649797 := by decide
  rcases family_descends (prefixWord ++ tailWord_649797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649856 : List Nat := [2, 1, 1, 2, 1, 14]
def baseStart_649856 : Nat := 118140960795 + 649856 * 2 ^ 59
def prefixEnd_649856 : Nat := 4983230072969 + 3 ^ 40 * 649856 * 2
def baseEnd_649856 : Nat := 5492814554869377269323

theorem tailTrace_649856 : CollatzResearch.WordTrace tailWord_649856 prefixEnd_649856 5492814554869377269323 := by
  unfold tailWord_649856
  simp only [CollatzResearch.WordTrace]
  refine ⟨11851097766845086706908711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15801463689126782275878281 11851097766845086706908711)
  ·
    refine ⟨17776646650267630060363067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11851097766845086706908711 17776646650267630060363067)
    ·
      refine ⟨26664969975401445090544601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17776646650267630060363067 26664969975401445090544601)
      ·
        refine ⟨19998727481551083817908451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26664969975401445090544601 19998727481551083817908451)
        ·
          refine ⟨29998091222326625726862677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19998727481551083817908451 29998091222326625726862677)
          ·
            refine ⟨5492814554869377269323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 29998091222326625726862677 5492814554869377269323)
            ·
              rfl

theorem cell21_649856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 14].length) (baseStart_649856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649856 prefixEnd_649856 := by exact prefixLift 649856
  have htrace : WordTrace (prefixWord ++ tailWord_649856) baseStart_649856 baseEnd_649856 := by
    simpa [prefixWord, tailWord_649856, baseEnd_649856] using wordTrace_append hprefix tailTrace_649856
  have hstable : (prefixWord ++ tailWord_649856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649856).length < 2 ^ (prefixWord ++ tailWord_649856).sum := by decide
  have hdescent : baseEnd_649856 < baseStart_649856 := by decide
  rcases family_descends (prefixWord ++ tailWord_649856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649876 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 4]
def baseStart_649876 : Nat := 118140960795 + 649876 * 2 ^ 59
def prefixEnd_649876 : Nat := 4983230072969 + 3 ^ 40 * 649876 * 2
def baseEnd_649876 : Nat := 148310557253957595938347

theorem tailTrace_649876 : CollatzResearch.WordTrace tailWord_649876 prefixEnd_649876 148310557253957595938347 := by
  unfold tailWord_649876
  simp only [CollatzResearch.WordTrace]
  refine ⟨11851462496808858414772741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15801949995745144553030321 11851462496808858414772741)
  ·
    refine ⟨2222149218151660952769889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11851462496808858414772741 2222149218151660952769889)
    ·
      refine ⟨1666611913613745714577417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2222149218151660952769889 1666611913613745714577417)
      ·
        refine ⟨1249958935210309285933063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1666611913613745714577417 1249958935210309285933063)
        ·
          refine ⟨1874938402815463928899595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249958935210309285933063 1874938402815463928899595)
          ·
            refine ⟨2812407604223195893349393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874938402815463928899595 2812407604223195893349393)
            ·
              refine ⟨2109305703167396920012045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2812407604223195893349393 2109305703167396920012045)
              ·
                refine ⟨790989638687773845004517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2109305703167396920012045 790989638687773845004517)
                ·
                  refine ⟨148310557253957595938347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 790989638687773845004517 148310557253957595938347)
                  ·
                    rfl

theorem cell21_649876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_649876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649876 prefixEnd_649876 := by exact prefixLift 649876
  have htrace : WordTrace (prefixWord ++ tailWord_649876) baseStart_649876 baseEnd_649876 := by
    simpa [prefixWord, tailWord_649876, baseEnd_649876] using wordTrace_append hprefix tailTrace_649876
  have hstable : (prefixWord ++ tailWord_649876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649876).length < 2 ^ (prefixWord ++ tailWord_649876).sum := by decide
  have hdescent : baseEnd_649876 < baseStart_649876 := by decide
  rcases family_descends (prefixWord ++ tailWord_649876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649910 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_649910 : Nat := 118140960795 + 649910 * 2 ^ 59
def prefixEnd_649910 : Nat := 4983230072969 + 3 ^ 40 * 649910 * 2
def baseEnd_649910 : Nat := 148318316517181092371611

theorem tailTrace_649910 : CollatzResearch.WordTrace tailWord_649910 prefixEnd_649910 148318316517181092371611 := by
  unfold tailWord_649910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1481510317218408789767699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15802776716996360424188789 1481510317218408789767699)
  ·
    refine ⟨2222265475827613184651549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1481510317218408789767699 2222265475827613184651549)
    ·
      refine ⟨833349553435354944244331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2222265475827613184651549 833349553435354944244331)
      ·
        refine ⟨1250024330153032416366497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833349553435354944244331 1250024330153032416366497)
        ·
          refine ⟨937518247614774312274873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1250024330153032416366497 937518247614774312274873)
          ·
            refine ⟨703138685711080734206155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 937518247614774312274873 703138685711080734206155)
            ·
              refine ⟨1054708028566621101309233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703138685711080734206155 1054708028566621101309233)
              ·
                refine ⟨791031021424965825981925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1054708028566621101309233 791031021424965825981925)
                ·
                  refine ⟨148318316517181092371611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 791031021424965825981925 148318316517181092371611)
                  ·
                    rfl

theorem cell21_649910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_649910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649910 prefixEnd_649910 := by exact prefixLift 649910
  have htrace : WordTrace (prefixWord ++ tailWord_649910) baseStart_649910 baseEnd_649910 := by
    simpa [prefixWord, tailWord_649910, baseEnd_649910] using wordTrace_append hprefix tailTrace_649910
  have hstable : (prefixWord ++ tailWord_649910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649910).length < 2 ^ (prefixWord ++ tailWord_649910).sum := by decide
  have hdescent : baseEnd_649910 < baseStart_649910 := by decide
  rcases family_descends (prefixWord ++ tailWord_649910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649972 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 5]
def baseStart_649972 : Nat := 118140960795 + 649972 * 2 ^ 59
def prefixEnd_649972 : Nat := 4983230072969 + 3 ^ 40 * 649972 * 2
def baseEnd_649972 : Nat := 148332465761882762338151

theorem tailTrace_649972 : CollatzResearch.WordTrace tailWord_649972 prefixEnd_649972 148332465761882762338151 := by
  unfold tailWord_649972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11853213200634962612520085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15804284267513283483360113 11853213200634962612520085)
  ·
    refine ⟨555619368779763872461879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11853213200634962612520085 555619368779763872461879)
    ·
      refine ⟨833429053169645808692819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555619368779763872461879 833429053169645808692819)
      ·
        refine ⟨1250143579754468713039229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833429053169645808692819 1250143579754468713039229)
        ·
          refine ⟨468803842407925767389711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1250143579754468713039229 468803842407925767389711)
          ·
            refine ⟨703205763611888651084567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468803842407925767389711 703205763611888651084567)
            ·
              refine ⟨1054808645417832976626851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703205763611888651084567 1054808645417832976626851)
              ·
                refine ⟨1582212968126749464940277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054808645417832976626851 1582212968126749464940277)
                ·
                  refine ⟨148332465761882762338151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1582212968126749464940277 148332465761882762338151)
                  ·
                    rfl

theorem cell21_649972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_649972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649972 prefixEnd_649972 := by exact prefixLift 649972
  have htrace : WordTrace (prefixWord ++ tailWord_649972) baseStart_649972 baseEnd_649972 := by
    simpa [prefixWord, tailWord_649972, baseEnd_649972] using wordTrace_append hprefix tailTrace_649972
  have hstable : (prefixWord ++ tailWord_649972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649972).length < 2 ^ (prefixWord ++ tailWord_649972).sum := by decide
  have hdescent : baseEnd_649972 < baseStart_649972 := by decide
  rcases family_descends (prefixWord ++ tailWord_649972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_649980 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 5]
def baseStart_649980 : Nat := 118140960795 + 649980 * 2 ^ 59
def prefixEnd_649980 : Nat := 4983230072969 + 3 ^ 40 * 649980 * 2
def baseEnd_649980 : Nat := 148334291470876526204801

theorem tailTrace_649980 : CollatzResearch.WordTrace tailWord_649980 prefixEnd_649980 148334291470876526204801 := by
  unfold tailWord_649980
  simp only [CollatzResearch.WordTrace]
  refine ⟨11853359092620471295665697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15804478790160628394220929 11853359092620471295665697)
  ·
    refine ⟨8890019319465353471749273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11853359092620471295665697 8890019319465353471749273)
    ·
      refine ⟨6667514489599015103811955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8890019319465353471749273 6667514489599015103811955)
      ·
        refine ⟨10001271734398522655717933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6667514489599015103811955 10001271734398522655717933)
        ·
          refine ⟨3750476900399445995894225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10001271734398522655717933 3750476900399445995894225)
          ·
            refine ⟨2812857675299584496920669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3750476900399445995894225 2812857675299584496920669)
            ·
              refine ⟨1054821628237344186345251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2812857675299584496920669 1054821628237344186345251)
              ·
                refine ⟨1582232442356016279517877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054821628237344186345251 1582232442356016279517877)
                ·
                  refine ⟨148334291470876526204801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1582232442356016279517877 148334291470876526204801)
                  ·
                    rfl

theorem cell21_649980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_649980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_649980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_649980 prefixEnd_649980 := by exact prefixLift 649980
  have htrace : WordTrace (prefixWord ++ tailWord_649980) baseStart_649980 baseEnd_649980 := by
    simpa [prefixWord, tailWord_649980, baseEnd_649980] using wordTrace_append hprefix tailTrace_649980
  have hstable : (prefixWord ++ tailWord_649980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_649980).length < 2 ^ (prefixWord ++ tailWord_649980).sum := by decide
  have hdescent : baseEnd_649980 < baseStart_649980 := by decide
  rcases family_descends (prefixWord ++ tailWord_649980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650039 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 5]
def baseStart_650039 : Nat := 118140960795 + 650039 * 2 ^ 59
def prefixEnd_650039 : Nat := 4983230072969 + 3 ^ 40 * 650039 * 2
def baseEnd_650039 : Nat := 148347756074705534721347

theorem tailTrace_650039 : CollatzResearch.WordTrace tailWord_650039 prefixEnd_650039 148347756074705534721347 := by
  unfold tailWord_650039
  simp only [CollatzResearch.WordTrace]
  refine ⟨23708870092027195667729171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15805913394684797111819447 23708870092027195667729171)
  ·
    refine ⟨35563305138040793501593757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23708870092027195667729171 35563305138040793501593757)
    ·
      refine ⟨13336239426765297563097659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35563305138040793501593757 13336239426765297563097659)
      ·
        refine ⟨20004359140147946344646489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13336239426765297563097659 20004359140147946344646489)
        ·
          refine ⟨15003269355110959758484867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20004359140147946344646489 15003269355110959758484867)
          ·
            refine ⟨22504904032666439637727301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15003269355110959758484867 22504904032666439637727301)
            ·
              refine ⟨4219669506124957432073869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22504904032666439637727301 4219669506124957432073869)
              ·
                refine ⟨1582376064796859037027701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4219669506124957432073869 1582376064796859037027701)
                ·
                  refine ⟨148347756074705534721347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1582376064796859037027701 148347756074705534721347)
                  ·
                    rfl

theorem cell21_650039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_650039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650039 prefixEnd_650039 := by exact prefixLift 650039
  have htrace : WordTrace (prefixWord ++ tailWord_650039) baseStart_650039 baseEnd_650039 := by
    simpa [prefixWord, tailWord_650039, baseEnd_650039] using wordTrace_append hprefix tailTrace_650039
  have hstable : (prefixWord ++ tailWord_650039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650039).length < 2 ^ (prefixWord ++ tailWord_650039).sum := by decide
  have hdescent : baseEnd_650039 < baseStart_650039 := by decide
  rcases family_descends (prefixWord ++ tailWord_650039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650042 : List Nat := [3, 1, 1, 1, 6, 2, 1, 6]
def baseStart_650042 : Nat := 118140960795 + 650042 * 2 ^ 59
def prefixEnd_650042 : Nat := 4983230072969 + 3 ^ 40 * 650042 * 2
def baseEnd_650042 : Nat := 49449480238526065390447

theorem tailTrace_650042 : CollatzResearch.WordTrace tailWord_650042 prefixEnd_650042 49449480238526065390447 := by
  unfold tailWord_650042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5927244877754081795022095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15805986340677551453392253 5927244877754081795022095)
  ·
    refine ⟨8890867316631122692533143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5927244877754081795022095 8890867316631122692533143)
    ·
      refine ⟨13336300974946684038799715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8890867316631122692533143 13336300974946684038799715)
      ·
        refine ⟨20004451462420026058199573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13336300974946684038799715 20004451462420026058199573)
        ·
          refine ⟨937708662300938721478105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20004451462420026058199573 937708662300938721478105)
          ·
            refine ⟨703281496725704041108579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 937708662300938721478105 703281496725704041108579)
            ·
              refine ⟨1054922245088556061662869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703281496725704041108579 1054922245088556061662869)
              ·
                refine ⟨49449480238526065390447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1054922245088556061662869 49449480238526065390447)
                ·
                  rfl

theorem cell21_650042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_650042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650042 prefixEnd_650042 := by exact prefixLift 650042
  have htrace : WordTrace (prefixWord ++ tailWord_650042) baseStart_650042 baseEnd_650042 := by
    simpa [prefixWord, tailWord_650042, baseEnd_650042] using wordTrace_append hprefix tailTrace_650042
  have hstable : (prefixWord ++ tailWord_650042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650042).length < 2 ^ (prefixWord ++ tailWord_650042).sum := by decide
  have hdescent : baseEnd_650042 < baseStart_650042 := by decide
  rcases family_descends (prefixWord ++ tailWord_650042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650073 : List Nat := [1, 2, 1, 2, 2, 5, 2, 3, 3]
def baseStart_650073 : Nat := 118140960795 + 650073 * 2 ^ 59
def prefixEnd_650073 : Nat := 4983230072969 + 3 ^ 40 * 650073 * 2
def baseEnd_650073 : Nat := 148355515337929031154611

theorem tailTrace_650073 : CollatzResearch.WordTrace tailWord_650073 prefixEnd_650073 148355515337929031154611 := by
  unfold tailWord_650073
  simp only [CollatzResearch.WordTrace]
  refine ⟨23710110173904019474466873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15806740115936012982977915 23710110173904019474466873)
  ·
    refine ⟨17782582630428014605850155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23710110173904019474466873 17782582630428014605850155)
    ·
      refine ⟨26673873945642021908775233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17782582630428014605850155 26673873945642021908775233)
      ·
        refine ⟨20005405459231516431581425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26673873945642021908775233 20005405459231516431581425)
        ·
          refine ⟨15004054094423637323686069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20005405459231516431581425 15004054094423637323686069)
          ·
            refine ⟨1406630071352215999095569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15004054094423637323686069 1406630071352215999095569)
            ·
              refine ⟨1054972553514161999321677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1406630071352215999095569 1054972553514161999321677)
              ·
                refine ⟨395614707567810749745629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1054972553514161999321677 395614707567810749745629)
                ·
                  refine ⟨148355515337929031154611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395614707567810749745629 148355515337929031154611)
                  ·
                    rfl

theorem cell21_650073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 3].length) (baseStart_650073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650073 prefixEnd_650073 := by exact prefixLift 650073
  have htrace : WordTrace (prefixWord ++ tailWord_650073) baseStart_650073 baseEnd_650073 := by
    simpa [prefixWord, tailWord_650073, baseEnd_650073] using wordTrace_append hprefix tailTrace_650073
  have hstable : (prefixWord ++ tailWord_650073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650073).length < 2 ^ (prefixWord ++ tailWord_650073).sum := by decide
  have hdescent : baseEnd_650073 < baseStart_650073 := by decide
  rcases family_descends (prefixWord ++ tailWord_650073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650087 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 4]
def baseStart_650087 : Nat := 118140960795 + 650087 * 2 ^ 59
def prefixEnd_650087 : Nat := 4983230072969 + 3 ^ 40 * 650087 * 2
def baseEnd_650087 : Nat := 148358710328668117921249

theorem tailTrace_650087 : CollatzResearch.WordTrace tailWord_650087 prefixEnd_650087 148358710328668117921249 := by
  unfold tailWord_650087
  simp only [CollatzResearch.WordTrace]
  refine ⟨23710620795853299865476515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15807080530568866576984343 23710620795853299865476515)
  ·
    refine ⟨35565931193779949798214773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23710620795853299865476515 35565931193779949798214773)
    ·
      refine ⟨3334306049416870293582635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35565931193779949798214773 3334306049416870293582635)
      ·
        refine ⟨5001459074125305440373953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3334306049416870293582635 5001459074125305440373953)
        ·
          refine ⟨3751094305593979080280465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5001459074125305440373953 3751094305593979080280465)
          ·
            refine ⟨2813320729195484310210349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3751094305593979080280465 2813320729195484310210349)
            ·
              refine ⟨1054995273448306616328881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2813320729195484310210349 1054995273448306616328881)
              ·
                refine ⟨791246455086229962246661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1054995273448306616328881 791246455086229962246661)
                ·
                  refine ⟨148358710328668117921249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 791246455086229962246661 148358710328668117921249)
                  ·
                    rfl

theorem cell21_650087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 4].length) (baseStart_650087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650087 prefixEnd_650087 := by exact prefixLift 650087
  have htrace : WordTrace (prefixWord ++ tailWord_650087) baseStart_650087 baseEnd_650087 := by
    simpa [prefixWord, tailWord_650087, baseEnd_650087] using wordTrace_append hprefix tailTrace_650087
  have hstable : (prefixWord ++ tailWord_650087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650087).length < 2 ^ (prefixWord ++ tailWord_650087).sum := by decide
  have hdescent : baseEnd_650087 < baseStart_650087 := by decide
  rcases family_descends (prefixWord ++ tailWord_650087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650115 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 5]
def baseStart_650115 : Nat := 118140960795 + 650115 * 2 ^ 59
def prefixEnd_650115 : Nat := 4983230072969 + 3 ^ 40 * 650115 * 2
def baseEnd_650115 : Nat := 148365100310146291454525

theorem tailTrace_650115 : CollatzResearch.WordTrace tailWord_650115 prefixEnd_650115 148365100310146291454525 := by
  unfold tailWord_650115
  simp only [CollatzResearch.WordTrace]
  refine ⟨23711642039751860647495799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15807761359834573764997199 23711642039751860647495799)
  ·
    refine ⟨35567463059627790971243699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23711642039751860647495799 35567463059627790971243699)
    ·
      refine ⟨53351194589441686456865549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35567463059627790971243699 53351194589441686456865549)
      ·
        refine ⟨20006697971040632421324581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53351194589441686456865549 20006697971040632421324581)
        ·
          refine ⟨3751255869570118578998359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20006697971040632421324581 3751255869570118578998359)
          ·
            refine ⟨5626883804355177868497539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751255869570118578998359 5626883804355177868497539)
            ·
              refine ⟨8440325706532766802746309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5626883804355177868497539 8440325706532766802746309)
              ·
                refine ⟨1582561069974893775514933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8440325706532766802746309 1582561069974893775514933)
                ·
                  refine ⟨148365100310146291454525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1582561069974893775514933 148365100310146291454525)
                  ·
                    rfl

theorem cell21_650115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_650115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650115 prefixEnd_650115 := by exact prefixLift 650115
  have htrace : WordTrace (prefixWord ++ tailWord_650115) baseStart_650115 baseEnd_650115 := by
    simpa [prefixWord, tailWord_650115, baseEnd_650115] using wordTrace_append hprefix tailTrace_650115
  have hstable : (prefixWord ++ tailWord_650115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650115).length < 2 ^ (prefixWord ++ tailWord_650115).sum := by decide
  have hdescent : baseEnd_650115 < baseStart_650115 := by decide
  rcases family_descends (prefixWord ++ tailWord_650115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650301 : List Nat := [1, 4, 1, 3, 1, 2, 3, 3, 3]
def baseStart_650301 : Nat := 118140960795 + 650301 * 2 ^ 59
def prefixEnd_650301 : Nat := 4983230072969 + 3 ^ 40 * 650301 * 2
def baseEnd_650301 : Nat := 148407548044251301354145

theorem tailTrace_650301 : CollatzResearch.WordTrace tailWord_650301 prefixEnd_650301 148407548044251301354145 := by
  unfold tailWord_650301
  simp only [CollatzResearch.WordTrace]
  refine ⟨23718426017078014413766757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15812284011385342942511171 23718426017078014413766757)
  ·
    refine ⟨4447204878202127702581267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23718426017078014413766757 4447204878202127702581267)
    ·
      refine ⟨6670807317303191553871901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4447204878202127702581267 6670807317303191553871901)
      ·
        refine ⟨2501552743988696832701963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6670807317303191553871901 2501552743988696832701963)
        ·
          refine ⟨3752329115983045249052945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501552743988696832701963 3752329115983045249052945)
          ·
            refine ⟨2814246836987283936789709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3752329115983045249052945 2814246836987283936789709)
            ·
              refine ⟨1055342563870231476296141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2814246836987283936789709 1055342563870231476296141)
              ·
                refine ⟨395753461451336803611053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1055342563870231476296141 395753461451336803611053)
                ·
                  refine ⟨148407548044251301354145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395753461451336803611053 148407548044251301354145)
                  ·
                    rfl

theorem cell21_650301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_650301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650301 prefixEnd_650301 := by exact prefixLift 650301
  have htrace : WordTrace (prefixWord ++ tailWord_650301) baseStart_650301 baseEnd_650301 := by
    simpa [prefixWord, tailWord_650301, baseEnd_650301] using wordTrace_append hprefix tailTrace_650301
  have hstable : (prefixWord ++ tailWord_650301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650301).length < 2 ^ (prefixWord ++ tailWord_650301).sum := by decide
  have hdescent : baseEnd_650301 < baseStart_650301 := by decide
  rcases family_descends (prefixWord ++ tailWord_650301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650366 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_650366 : Nat := 118140960795 + 650366 * 2 ^ 59
def prefixEnd_650366 : Nat := 4983230072969 + 3 ^ 40 * 650366 * 2
def baseEnd_650366 : Nat := 148422381929825632770679

theorem tailTrace_650366 : CollatzResearch.WordTrace tailWord_650366 prefixEnd_650366 148422381929825632770679 := by
  unfold tailWord_650366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2965099595230316314360369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15813864507895020343255301 2965099595230316314360369)
  ·
    refine ⟨2223824696422737235770277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2965099595230316314360369 2223824696422737235770277)
    ·
      refine ⟨416967130579263231706927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2223824696422737235770277 416967130579263231706927)
      ·
        refine ⟨625450695868894847560391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416967130579263231706927 625450695868894847560391)
        ·
          refine ⟨938176043803342271340587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625450695868894847560391 938176043803342271340587)
          ·
            refine ⟨1407264065705013407010881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938176043803342271340587 1407264065705013407010881)
            ·
              refine ⟨1055448049278760055258161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407264065705013407010881 1055448049278760055258161)
              ·
                refine ⟨791586036959070041443621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055448049278760055258161 791586036959070041443621)
                ·
                  refine ⟨148422381929825632770679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 791586036959070041443621 148422381929825632770679)
                  ·
                    rfl

theorem cell21_650366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_650366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650366 prefixEnd_650366 := by exact prefixLift 650366
  have htrace : WordTrace (prefixWord ++ tailWord_650366) baseStart_650366 baseEnd_650366 := by
    simpa [prefixWord, tailWord_650366, baseEnd_650366] using wordTrace_append hprefix tailTrace_650366
  have hstable : (prefixWord ++ tailWord_650366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650366).length < 2 ^ (prefixWord ++ tailWord_650366).sum := by decide
  have hdescent : baseEnd_650366 < baseStart_650366 := by decide
  rcases family_descends (prefixWord ++ tailWord_650366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650377 : List Nat := [1, 2, 1, 1, 4, 3, 4, 2, 3]
def baseStart_650377 : Nat := 118140960795 + 650377 * 2 ^ 59
def prefixEnd_650377 : Nat := 4983230072969 + 3 ^ 40 * 650377 * 2
def baseEnd_650377 : Nat := 148424892279692058087323

theorem tailTrace_650377 : CollatzResearch.WordTrace tailWord_650377 prefixEnd_650377 148424892279692058087323 := by
  unfold tailWord_650377
  simp only [CollatzResearch.WordTrace]
  refine ⟨23721197964802679393533385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15814131976535119595688923 23721197964802679393533385)
  ·
    refine ⟨17790898473602009545150039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23721197964802679393533385 17790898473602009545150039)
    ·
      refine ⟨26686347710403014317725059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17790898473602009545150039 26686347710403014317725059)
      ·
        refine ⟨40029521565604521476587589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26686347710403014317725059 40029521565604521476587589)
        ·
          refine ⟨7505535293550847776860173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40029521565604521476587589 7505535293550847776860173)
          ·
            refine ⟨2814575735081567916322565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7505535293550847776860173 2814575735081567916322565)
            ·
              refine ⟨527732950327793984310481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2814575735081567916322565 527732950327793984310481)
              ·
                refine ⟨395799712745845488232861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527732950327793984310481 395799712745845488232861)
                ·
                  refine ⟨148424892279692058087323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395799712745845488232861 148424892279692058087323)
                  ·
                    rfl

theorem cell21_650377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 3].length) (baseStart_650377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650377 prefixEnd_650377 := by exact prefixLift 650377
  have htrace : WordTrace (prefixWord ++ tailWord_650377) baseStart_650377 baseEnd_650377 := by
    simpa [prefixWord, tailWord_650377, baseEnd_650377] using wordTrace_append hprefix tailTrace_650377
  have hstable : (prefixWord ++ tailWord_650377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650377).length < 2 ^ (prefixWord ++ tailWord_650377).sum := by decide
  have hdescent : baseEnd_650377 < baseStart_650377 := by decide
  rcases family_descends (prefixWord ++ tailWord_650377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650405 : List Nat := [1, 3, 1, 2, 1, 5, 3, 5]
def baseStart_650405 : Nat := 118140960795 + 650405 * 2 ^ 59
def prefixEnd_650405 : Nat := 4983230072969 + 3 ^ 40 * 650405 * 2
def baseEnd_650405 : Nat := 49477094087056743873533

theorem tailTrace_650405 : CollatzResearch.WordTrace tailWord_650405 prefixEnd_650405 49477094087056743873533 := by
  unfold tailWord_650405
  simp only [CollatzResearch.WordTrace]
  refine ⟨23722219208701240175552669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15814812805800826783701779 23722219208701240175552669)
  ·
    refine ⟨8895832203262965065832251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23722219208701240175552669 8895832203262965065832251)
    ·
      refine ⟨13343748304894447598748377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8895832203262965065832251 13343748304894447598748377)
      ·
        refine ⟨10007811228670835699061283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13343748304894447598748377 10007811228670835699061283)
        ·
          refine ⟨15011716843006253548591925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10007811228670835699061283 15011716843006253548591925)
          ·
            refine ⟨1407348454031836270180493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15011716843006253548591925 1407348454031836270180493)
            ·
              refine ⟨527755670261938601317685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1407348454031836270180493 527755670261938601317685)
              ·
                refine ⟨49477094087056743873533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 527755670261938601317685 49477094087056743873533)
                ·
                  rfl

theorem cell21_650405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 5].length) (baseStart_650405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650405 prefixEnd_650405 := by exact prefixLift 650405
  have htrace : WordTrace (prefixWord ++ tailWord_650405) baseStart_650405 baseEnd_650405 := by
    simpa [prefixWord, tailWord_650405, baseEnd_650405] using wordTrace_append hprefix tailTrace_650405
  have hstable : (prefixWord ++ tailWord_650405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650405).length < 2 ^ (prefixWord ++ tailWord_650405).sum := by decide
  have hdescent : baseEnd_650405 < baseStart_650405 := by decide
  rcases family_descends (prefixWord ++ tailWord_650405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650464 : List Nat := [2, 1, 1, 3, 1, 5, 1, 7]
def baseStart_650464 : Nat := 118140960795 + 650464 * 2 ^ 59
def prefixEnd_650464 : Nat := 4983230072969 + 3 ^ 40 * 650464 * 2
def baseEnd_650464 : Nat := 49481582288333080045715

theorem tailTrace_650464 : CollatzResearch.WordTrace tailWord_650464 prefixEnd_650464 49481582288333080045715 := by
  unfold tailWord_650464
  simp only [CollatzResearch.WordTrace]
  refine ⟨11862185557743746625975223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15816247410324995501300297 11862185557743746625975223)
  ·
    refine ⟨17793278336615619938962835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11862185557743746625975223 17793278336615619938962835)
    ·
      refine ⟨26689917504923429908444253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17793278336615619938962835 26689917504923429908444253)
      ·
        refine ⟨10008719064346286215666595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26689917504923429908444253 10008719064346286215666595)
        ·
          refine ⟨15013078596519429323499893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10008719064346286215666595 15013078596519429323499893)
          ·
            refine ⟨1407476118423696499078115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15013078596519429323499893 1407476118423696499078115)
            ·
              refine ⟨2111214177635544748617173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407476118423696499078115 2111214177635544748617173)
              ·
                refine ⟨49481582288333080045715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2111214177635544748617173 49481582288333080045715)
                ·
                  rfl

theorem cell21_650464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_650464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650464 prefixEnd_650464 := by exact prefixLift 650464
  have htrace : WordTrace (prefixWord ++ tailWord_650464) baseStart_650464 baseEnd_650464 := by
    simpa [prefixWord, tailWord_650464, baseEnd_650464] using wordTrace_append hprefix tailTrace_650464
  have hstable : (prefixWord ++ tailWord_650464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650464).length < 2 ^ (prefixWord ++ tailWord_650464).sum := by decide
  have hdescent : baseEnd_650464 < baseStart_650464 := by decide
  rcases family_descends (prefixWord ++ tailWord_650464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650495 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 5]
def baseStart_650495 : Nat := 118140960795 + 650495 * 2 ^ 59
def prefixEnd_650495 : Nat := 4983230072969 + 3 ^ 40 * 650495 * 2
def baseEnd_650495 : Nat := 148451821487350075120415

theorem tailTrace_650495 : CollatzResearch.WordTrace tailWord_650495 prefixEnd_650495 148451821487350075120415 := by
  unfold tailWord_650495
  simp only [CollatzResearch.WordTrace]
  refine ⟨23725501778375185546328939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15817001185583457030885959 23725501778375185546328939)
  ·
    refine ⟨35588252667562778319493409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23725501778375185546328939 35588252667562778319493409)
    ·
      refine ⟨26691189500672083739620057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35588252667562778319493409 26691189500672083739620057)
      ·
        refine ⟨20018392125504062804715043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26691189500672083739620057 20018392125504062804715043)
        ·
          refine ⟨30027588188256094207072565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20018392125504062804715043 30027588188256094207072565)
          ·
            refine ⟨2815086392649008831913053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30027588188256094207072565 2815086392649008831913053)
            ·
              refine ⟨1055657397243378311967395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2815086392649008831913053 1055657397243378311967395)
              ·
                refine ⟨1583486095865067467951093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055657397243378311967395 1583486095865067467951093)
                ·
                  refine ⟨148451821487350075120415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1583486095865067467951093 148451821487350075120415)
                  ·
                    rfl

theorem cell21_650495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 5].length) (baseStart_650495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650495 prefixEnd_650495 := by exact prefixLift 650495
  have htrace : WordTrace (prefixWord ++ tailWord_650495) baseStart_650495 baseEnd_650495 := by
    simpa [prefixWord, tailWord_650495, baseEnd_650495] using wordTrace_append hprefix tailTrace_650495
  have hstable : (prefixWord ++ tailWord_650495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650495).length < 2 ^ (prefixWord ++ tailWord_650495).sum := by decide
  have hdescent : baseEnd_650495 < baseStart_650495 := by decide
  rcases family_descends (prefixWord ++ tailWord_650495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650498 : List Nat := [3, 4, 1, 1, 3, 1, 2, 6]
def baseStart_650498 : Nat := 118140960795 + 650498 * 2 ^ 59
def prefixEnd_650498 : Nat := 4983230072969 + 3 ^ 40 * 650498 * 2
def baseEnd_650498 : Nat := 49484168709407578856803

theorem tailTrace_650498 : CollatzResearch.WordTrace tailWord_650498 prefixEnd_650498 49484168709407578856803 := by
  unfold tailWord_650498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5931402799341079264672037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15817074131576211372458765 5931402799341079264672037)
  ·
    refine ⟨1112138024876452362126007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5931402799341079264672037 1112138024876452362126007)
    ·
      refine ⟨1668207037314678543189011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112138024876452362126007 1668207037314678543189011)
      ·
        refine ⟨2502310555972017814783517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1668207037314678543189011 2502310555972017814783517)
        ·
          refine ⟨938366458489506680543819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2502310555972017814783517 938366458489506680543819)
          ·
            refine ⟨1407549687734260020815729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938366458489506680543819 1407549687734260020815729)
            ·
              refine ⟨1055662265800695015611797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407549687734260020815729 1055662265800695015611797)
              ·
                refine ⟨49484168709407578856803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1055662265800695015611797 49484168709407578856803)
                ·
                  rfl

theorem cell21_650498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_650498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650498 prefixEnd_650498 := by exact prefixLift 650498
  have htrace : WordTrace (prefixWord ++ tailWord_650498) baseStart_650498 baseEnd_650498 := by
    simpa [prefixWord, tailWord_650498, baseEnd_650498] using wordTrace_append hprefix tailTrace_650498
  have hstable : (prefixWord ++ tailWord_650498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650498).length < 2 ^ (prefixWord ++ tailWord_650498).sum := by decide
  have hdescent : baseEnd_650498 < baseStart_650498 := by decide
  rcases family_descends (prefixWord ++ tailWord_650498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650546 : List Nat := [3, 2, 1, 1, 4, 3, 2, 2, 3]
def baseStart_650546 : Nat := 118140960795 + 650546 * 2 ^ 59
def prefixEnd_650546 : Nat := 4983230072969 + 3 ^ 40 * 650546 * 2
def baseEnd_650546 : Nat := 148463460382185319770311

theorem tailTrace_650546 : CollatzResearch.WordTrace tailWord_650546 prefixEnd_650546 148463460382185319770311 := by
  unfold tailWord_650546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5931840475297605314108873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15818241267460280837623661 5931840475297605314108873)
  ·
    refine ⟨4448880356473203985581655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5931840475297605314108873 4448880356473203985581655)
    ·
      refine ⟨6673320534709805978372483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4448880356473203985581655 6673320534709805978372483)
      ·
        refine ⟨10009980802064708967558725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6673320534709805978372483 10009980802064708967558725)
        ·
          refine ⟨1876871400387132931417261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10009980802064708967558725 1876871400387132931417261)
          ·
            refine ⟨703826775145174849281473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1876871400387132931417261 703826775145174849281473)
            ·
              refine ⟨527870081358881136961105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703826775145174849281473 527870081358881136961105)
              ·
                refine ⟨395902561019160852720829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527870081358881136961105 395902561019160852720829)
                ·
                  refine ⟨148463460382185319770311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395902561019160852720829 148463460382185319770311)
                  ·
                    rfl

theorem cell21_650546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_650546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650546 prefixEnd_650546 := by exact prefixLift 650546
  have htrace : WordTrace (prefixWord ++ tailWord_650546) baseStart_650546 baseEnd_650546 := by
    simpa [prefixWord, tailWord_650546, baseEnd_650546] using wordTrace_append hprefix tailTrace_650546
  have hstable : (prefixWord ++ tailWord_650546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650546).length < 2 ^ (prefixWord ++ tailWord_650546).sum := by decide
  have hdescent : baseEnd_650546 < baseStart_650546 := by decide
  rcases family_descends (prefixWord ++ tailWord_650546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650844 : List Nat := [2, 2, 4, 1, 2, 1, 1, 8]
def baseStart_650844 : Nat := 118140960795 + 650844 * 2 ^ 59
def prefixEnd_650844 : Nat := 4983230072969 + 3 ^ 40 * 650844 * 2
def baseEnd_650844 : Nat := 49510489347401007934345

theorem tailTrace_650844 : CollatzResearch.WordTrace tailWord_650844 prefixEnd_650844 49510489347401007934345 := by
  unfold tailWord_650844
  simp only [CollatzResearch.WordTrace]
  refine ⟨11869115427055409075391793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15825487236073878767189057 11869115427055409075391793)
  ·
    refine ⟨8901836570291556806543845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11869115427055409075391793 8901836570291556806543845)
    ·
      refine ⟨1669094356929666901226971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8901836570291556806543845 1669094356929666901226971)
      ·
        refine ⟨2503641535394500351840457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669094356929666901226971 2503641535394500351840457)
        ·
          refine ⟨1877731151545875263880343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2503641535394500351840457 1877731151545875263880343)
          ·
            refine ⟨2816596727318812895820515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877731151545875263880343 2816596727318812895820515)
            ·
              refine ⟨4224895090978219343730773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816596727318812895820515 4224895090978219343730773)
              ·
                refine ⟨49510489347401007934345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4224895090978219343730773 49510489347401007934345)
                ·
                  rfl

theorem cell21_650844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_650844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650844 prefixEnd_650844 := by exact prefixLift 650844
  have htrace : WordTrace (prefixWord ++ tailWord_650844) baseStart_650844 baseEnd_650844 := by
    simpa [prefixWord, tailWord_650844, baseEnd_650844] using wordTrace_append hprefix tailTrace_650844
  have hstable : (prefixWord ++ tailWord_650844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650844).length < 2 ^ (prefixWord ++ tailWord_650844).sum := by decide
  have hdescent : baseEnd_650844 < baseStart_650844 := by decide
  rcases family_descends (prefixWord ++ tailWord_650844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650875 : List Nat := [1, 1, 1, 1, 1, 4, 4, 5, 3]
def baseStart_650875 : Nat := 118140960795 + 650875 * 2 ^ 59
def prefixEnd_650875 : Nat := 4983230072969 + 3 ^ 40 * 650875 * 2
def baseEnd_650875 : Nat := 148538542664553858786305

theorem tailTrace_650875 : CollatzResearch.WordTrace tailWord_650875 prefixEnd_650875 148538542664553858786305 := by
  unfold tailWord_650875
  simp only [CollatzResearch.WordTrace]
  refine ⟨23739361516998510445162079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15826241011332340296774719 23739361516998510445162079)
  ·
    refine ⟨35609042275497765667743119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23739361516998510445162079 35609042275497765667743119)
    ·
      refine ⟨53413563413246648501614679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35609042275497765667743119 53413563413246648501614679)
      ·
        refine ⟨80120345119869972752422019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53413563413246648501614679 80120345119869972752422019)
        ·
          refine ⟨120180517679804959128633029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80120345119869972752422019 120180517679804959128633029)
          ·
            refine ⟨22533847064963429836618693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120180517679804959128633029 22533847064963429836618693)
            ·
              refine ⟨4225096324680643094366005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22533847064963429836618693 4225096324680643094366005)
              ·
                refine ⟨396102780438810290096813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4225096324680643094366005 396102780438810290096813)
                ·
                  refine ⟨148538542664553858786305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396102780438810290096813 148538542664553858786305)
                  ·
                    rfl

theorem cell21_650875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 3].length) (baseStart_650875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650875 prefixEnd_650875 := by exact prefixLift 650875
  have htrace : WordTrace (prefixWord ++ tailWord_650875) baseStart_650875 baseEnd_650875 := by
    simpa [prefixWord, tailWord_650875, baseEnd_650875] using wordTrace_append hprefix tailTrace_650875
  have hstable : (prefixWord ++ tailWord_650875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650875).length < 2 ^ (prefixWord ++ tailWord_650875).sum := by decide
  have hdescent : baseEnd_650875 < baseStart_650875 := by decide
  rcases family_descends (prefixWord ++ tailWord_650875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650889 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 4]
def baseStart_650889 : Nat := 118140960795 + 650889 * 2 ^ 59
def prefixEnd_650889 : Nat := 4983230072969 + 3 ^ 40 * 650889 * 2
def baseEnd_650889 : Nat := 148541737655292945552943

theorem tailTrace_650889 : CollatzResearch.WordTrace tailWord_650889 prefixEnd_650889 148541737655292945552943 := by
  unfold tailWord_650889
  simp only [CollatzResearch.WordTrace]
  refine ⟨23739872138947790836171721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15826581425965193890781147 23739872138947790836171721)
  ·
    refine ⟨17804904104210843127128791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23739872138947790836171721 17804904104210843127128791)
    ·
      refine ⟨26707356156316264690693187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17804904104210843127128791 26707356156316264690693187)
      ·
        refine ⟨40061034234474397036039781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26707356156316264690693187 40061034234474397036039781)
        ·
          refine ⟨7511443918963949444257459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40061034234474397036039781 7511443918963949444257459)
          ·
            refine ⟨11267165878445924166386189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7511443918963949444257459 11267165878445924166386189)
            ·
              refine ⟨4225187204417221562394821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11267165878445924166386189 4225187204417221562394821)
              ·
                refine ⟨792222600828229042949029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4225187204417221562394821 792222600828229042949029)
                ·
                  refine ⟨148541737655292945552943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 792222600828229042949029 148541737655292945552943)
                  ·
                    rfl

theorem cell21_650889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_650889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650889 prefixEnd_650889 := by exact prefixLift 650889
  have htrace : WordTrace (prefixWord ++ tailWord_650889) baseStart_650889 baseEnd_650889 := by
    simpa [prefixWord, tailWord_650889, baseEnd_650889] using wordTrace_append hprefix tailTrace_650889
  have hstable : (prefixWord ++ tailWord_650889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650889).length < 2 ^ (prefixWord ++ tailWord_650889).sum := by decide
  have hdescent : baseEnd_650889 < baseStart_650889 := by decide
  rcases family_descends (prefixWord ++ tailWord_650889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650926 : List Nat := [4, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_650926 : Nat := 118140960795 + 650926 * 2 ^ 59
def prefixEnd_650926 : Nat := 4983230072969 + 3 ^ 40 * 650926 * 2
def baseEnd_650926 : Nat := 148550181559389103436201

theorem tailTrace_650926 : CollatzResearch.WordTrace tailWord_650926 prefixEnd_650926 148550181559389103436201 := by
  unfold tailWord_650926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2967652704976718269408579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15827481093209164103512421 2967652704976718269408579)
  ·
    refine ⟨4451479057465077404112869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2967652704976718269408579 4451479057465077404112869)
    ·
      refine ⟨834652323274702013271163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4451479057465077404112869 834652323274702013271163)
      ·
        refine ⟨1251978484912053019906745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834652323274702013271163 1251978484912053019906745)
        ·
          refine ⟨938983863684039764930059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1251978484912053019906745 938983863684039764930059)
          ·
            refine ⟨1408475795526059647395089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938983863684039764930059 1408475795526059647395089)
            ·
              refine ⟨1056356846644544735546317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408475795526059647395089 1056356846644544735546317)
              ·
                refine ⟨396133817491704275829869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1056356846644544735546317 396133817491704275829869)
                ·
                  refine ⟨148550181559389103436201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396133817491704275829869 148550181559389103436201)
                  ·
                    rfl

theorem cell21_650926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_650926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650926 prefixEnd_650926 := by exact prefixLift 650926
  have htrace : WordTrace (prefixWord ++ tailWord_650926) baseStart_650926 baseEnd_650926 := by
    simpa [prefixWord, tailWord_650926, baseEnd_650926] using wordTrace_append hprefix tailTrace_650926
  have hstable : (prefixWord ++ tailWord_650926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650926).length < 2 ^ (prefixWord ++ tailWord_650926).sum := by decide
  have hdescent : baseEnd_650926 < baseStart_650926 := by decide
  rcases family_descends (prefixWord ++ tailWord_650926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_650951 : List Nat := [1, 1, 4, 1, 1, 1, 3, 6, 3]
def baseStart_650951 : Nat := 118140960795 + 650951 * 2 ^ 59
def prefixEnd_650951 : Nat := 4983230072969 + 3 ^ 40 * 650951 * 2
def baseEnd_650951 : Nat := 148555886899994615519483

theorem tailTrace_650951 : CollatzResearch.WordTrace tailWord_650951 prefixEnd_650951 148555886899994615519483 := by
  unfold tailWord_650951
  simp only [CollatzResearch.WordTrace]
  refine ⟨23742133464723175424928707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15828088976482116949952471 23742133464723175424928707)
  ·
    refine ⟨35613200197084763137393061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23742133464723175424928707 35613200197084763137393061)
    ·
      refine ⟨6677475036953393088261199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35613200197084763137393061 6677475036953393088261199)
      ·
        refine ⟨10016212555430089632391799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6677475036953393088261199 10016212555430089632391799)
        ·
          refine ⟨15024318833145134448587699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10016212555430089632391799 15024318833145134448587699)
          ·
            refine ⟨22536478249717701672881549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15024318833145134448587699 22536478249717701672881549)
            ·
              refine ⟨8451179343644138127330581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22536478249717701672881549 8451179343644138127330581)
              ·
                refine ⟨396149031733318974718621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8451179343644138127330581 396149031733318974718621)
                ·
                  refine ⟨148555886899994615519483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396149031733318974718621 148555886899994615519483)
                  ·
                    rfl

theorem cell21_650951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 3].length) (baseStart_650951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_650951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_650951 prefixEnd_650951 := by exact prefixLift 650951
  have htrace : WordTrace (prefixWord ++ tailWord_650951) baseStart_650951 baseEnd_650951 := by
    simpa [prefixWord, tailWord_650951, baseEnd_650951] using wordTrace_append hprefix tailTrace_650951
  have hstable : (prefixWord ++ tailWord_650951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_650951).length < 2 ^ (prefixWord ++ tailWord_650951).sum := by decide
  have hdescent : baseEnd_650951 < baseStart_650951 := by decide
  rcases family_descends (prefixWord ++ tailWord_650951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651058 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_651058 : Nat := 118140960795 + 651058 * 2 ^ 59
def prefixEnd_651058 : Nat := 4983230072969 + 3 ^ 40 * 651058 * 2
def baseEnd_651058 : Nat := 148580305757786207235931

theorem tailTrace_651058 : CollatzResearch.WordTrace tailWord_651058 prefixEnd_651058 148580305757786207235931 := by
  unfold tailWord_651058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5936509018833883174768457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15830690716890355132715885 5936509018833883174768457)
  ·
    refine ⟨4452381764125412381076343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5936509018833883174768457 4452381764125412381076343)
    ·
      refine ⟨6678572646188118571614515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4452381764125412381076343 6678572646188118571614515)
      ·
        refine ⟨10017858969282177857421773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6678572646188118571614515 10017858969282177857421773)
        ·
          refine ⟨3756697113480816696533165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10017858969282177857421773 3756697113480816696533165)
          ·
            refine ⟨1408761417555306261199937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3756697113480816696533165 1408761417555306261199937)
            ·
              refine ⟨1056571063166479695899953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408761417555306261199937 1056571063166479695899953)
              ·
                refine ⟨792428297374859771924965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1056571063166479695899953 792428297374859771924965)
                ·
                  refine ⟨148580305757786207235931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 792428297374859771924965 148580305757786207235931)
                  ·
                    rfl

theorem cell21_651058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_651058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651058 prefixEnd_651058 := by exact prefixLift 651058
  have htrace : WordTrace (prefixWord ++ tailWord_651058) baseStart_651058 baseEnd_651058 := by
    simpa [prefixWord, tailWord_651058, baseEnd_651058] using wordTrace_append hprefix tailTrace_651058
  have hstable : (prefixWord ++ tailWord_651058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651058).length < 2 ^ (prefixWord ++ tailWord_651058).sum := by decide
  have hdescent : baseEnd_651058 < baseStart_651058 := by decide
  rcases family_descends (prefixWord ++ tailWord_651058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651103 : List Nat := [1, 1, 2, 3, 1, 4, 1, 5, 3]
def baseStart_651103 : Nat := 118140960795 + 651103 * 2 ^ 59
def prefixEnd_651103 : Nat := 4983230072969 + 3 ^ 40 * 651103 * 2
def baseEnd_651103 : Nat := 148590575370876128985839

theorem tailTrace_651103 : CollatzResearch.WordTrace tailWord_651103 prefixEnd_651103 148590575370876128985839 := by
  unfold tailWord_651103
  simp only [CollatzResearch.WordTrace]
  refine ⟨23747677360172505384461963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15831784906781670256307975 23747677360172505384461963)
  ·
    refine ⟨35621516040258758076692945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23747677360172505384461963 35621516040258758076692945)
    ·
      refine ⟨26716137030194068557519709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35621516040258758076692945 26716137030194068557519709)
      ·
        refine ⟨10018551386322775709069891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26716137030194068557519709 10018551386322775709069891)
        ·
          refine ⟨15027827079484163563604837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10018551386322775709069891 15027827079484163563604837)
          ·
            refine ⟨2817717577403280668175907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15027827079484163563604837 2817717577403280668175907)
            ·
              refine ⟨4226576366104921002263861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817717577403280668175907 4226576366104921002263861)
              ·
                refine ⟨396241534322336343962237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4226576366104921002263861 396241534322336343962237)
                ·
                  refine ⟨148590575370876128985839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396241534322336343962237 148590575370876128985839)
                  ·
                    rfl

theorem cell21_651103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 3].length) (baseStart_651103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651103 prefixEnd_651103 := by exact prefixLift 651103
  have htrace : WordTrace (prefixWord ++ tailWord_651103) baseStart_651103 baseEnd_651103 := by
    simpa [prefixWord, tailWord_651103, baseEnd_651103] using wordTrace_append hprefix tailTrace_651103
  have hstable : (prefixWord ++ tailWord_651103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651103).length < 2 ^ (prefixWord ++ tailWord_651103).sum := by decide
  have hdescent : baseEnd_651103 < baseStart_651103 := by decide
  rcases family_descends (prefixWord ++ tailWord_651103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651193 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 4]
def baseStart_651193 : Nat := 118140960795 + 651193 * 2 ^ 59
def prefixEnd_651193 : Nat := 4983230072969 + 3 ^ 40 * 651193 * 2
def baseEnd_651193 : Nat := 148611114597055972485655

theorem tailTrace_651193 : CollatzResearch.WordTrace tailWord_651193 prefixEnd_651193 148611114597055972485655 := by
  unfold tailWord_651193
  simp only [CollatzResearch.WordTrace]
  refine ⟨23750959929846450755238233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15833973286564300503492155 23750959929846450755238233)
  ·
    refine ⟨17813219947384838066428675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23750959929846450755238233 17813219947384838066428675)
    ·
      refine ⟨26719829921077257099643013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17813219947384838066428675 26719829921077257099643013)
      ·
        refine ⟨5009968110201985706183065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26719829921077257099643013 5009968110201985706183065)
        ·
          refine ⟨3757476082651489279637299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5009968110201985706183065 3757476082651489279637299)
          ·
            refine ⟨5636214123977233919455949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757476082651489279637299 5636214123977233919455949)
            ·
              refine ⟨2113580296491462719795981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5636214123977233919455949 2113580296491462719795981)
              ·
                refine ⟨792592611184298519923493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2113580296491462719795981 792592611184298519923493)
                ·
                  refine ⟨148611114597055972485655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 792592611184298519923493 148611114597055972485655)
                  ·
                    rfl

theorem cell21_651193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_651193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651193 prefixEnd_651193 := by exact prefixLift 651193
  have htrace : WordTrace (prefixWord ++ tailWord_651193) baseStart_651193 baseEnd_651193 := by
    simpa [prefixWord, tailWord_651193, baseEnd_651193] using wordTrace_append hprefix tailTrace_651193
  have hstable : (prefixWord ++ tailWord_651193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651193).length < 2 ^ (prefixWord ++ tailWord_651193).sum := by decide
  have hdescent : baseEnd_651193 < baseStart_651193 := by decide
  rcases family_descends (prefixWord ++ tailWord_651193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651314 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_651314 : Nat := 118140960795 + 651314 * 2 ^ 59
def prefixEnd_651314 : Nat := 4983230072969 + 3 ^ 40 * 651314 * 2
def baseEnd_651314 : Nat := 148638728445586650968741

theorem tailTrace_651314 : CollatzResearch.WordTrace tailWord_651314 prefixEnd_651314 148638728445586650968741 := by
  unfold tailWord_651314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5938843290602022105098249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15836915441605392280261997 5938843290602022105098249)
  ·
    refine ⟨4454132467951516578823687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5938843290602022105098249 4454132467951516578823687)
    ·
      refine ⟨6681198701927274868235531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4454132467951516578823687 6681198701927274868235531)
      ·
        refine ⟨10021798052890912302353297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6681198701927274868235531 10021798052890912302353297)
        ·
          refine ⟨7516348539668184226764973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10021798052890912302353297 7516348539668184226764973)
          ·
            refine ⟨2818630702375569085036865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7516348539668184226764973 2818630702375569085036865)
            ·
              refine ⟨2113973026781676813777649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2818630702375569085036865 2113973026781676813777649)
              ·
                refine ⟨1585479770086257610333237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2113973026781676813777649 1585479770086257610333237)
                ·
                  refine ⟨148638728445586650968741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1585479770086257610333237 148638728445586650968741)
                  ·
                    rfl

theorem cell21_651314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_651314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651314 prefixEnd_651314 := by exact prefixLift 651314
  have htrace : WordTrace (prefixWord ++ tailWord_651314) baseStart_651314 baseEnd_651314 := by
    simpa [prefixWord, tailWord_651314, baseEnd_651314] using wordTrace_append hprefix tailTrace_651314
  have hstable : (prefixWord ++ tailWord_651314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651314).length < 2 ^ (prefixWord ++ tailWord_651314).sum := by decide
  have hdescent : baseEnd_651314 < baseStart_651314 := by decide
  rcases family_descends (prefixWord ++ tailWord_651314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651328 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_651328 : Nat := 118140960795 + 651328 * 2 ^ 59
def prefixEnd_651328 : Nat := 4983230072969 + 3 ^ 40 * 651328 * 2
def baseEnd_651328 : Nat := 148641923436325737735379

theorem tailTrace_651328 : CollatzResearch.WordTrace tailWord_651328 prefixEnd_651328 148641923436325737735379 := by
  unfold tailWord_651328
  simp only [CollatzResearch.WordTrace]
  refine ⟨11877941892178684405701319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15837255856238245874268425 11877941892178684405701319)
  ·
    refine ⟨17816912838268026608551979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11877941892178684405701319 17816912838268026608551979)
    ·
      refine ⟨26725369257402039912827969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17816912838268026608551979 26725369257402039912827969)
      ·
        refine ⟨20044026943051529934620977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26725369257402039912827969 20044026943051529934620977)
        ·
          refine ⟨15033020207288647450965733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20044026943051529934620977 15033020207288647450965733)
          ·
            refine ⟨2818691288866621397056075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15033020207288647450965733 2818691288866621397056075)
            ·
              refine ⟨4228036933299932095584113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2818691288866621397056075 4228036933299932095584113)
              ·
                refine ⟨3171027699974949071688085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4228036933299932095584113 3171027699974949071688085)
                ·
                  refine ⟨148641923436325737735379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3171027699974949071688085 148641923436325737735379)
                  ·
                    rfl

theorem cell21_651328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_651328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651328 prefixEnd_651328 := by exact prefixLift 651328
  have htrace : WordTrace (prefixWord ++ tailWord_651328) baseStart_651328 baseEnd_651328 := by
    simpa [prefixWord, tailWord_651328, baseEnd_651328] using wordTrace_append hprefix tailTrace_651328
  have hstable : (prefixWord ++ tailWord_651328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651328).length < 2 ^ (prefixWord ++ tailWord_651328).sum := by decide
  have hdescent : baseEnd_651328 < baseStart_651328 := by decide
  rcases family_descends (prefixWord ++ tailWord_651328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651421 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 4]
def baseStart_651421 : Nat := 118140960795 + 651421 * 2 ^ 59
def prefixEnd_651421 : Nat := 4983230072969 + 3 ^ 40 * 651421 * 2
def baseEnd_651421 : Nat := 148663147303378242685189

theorem tailTrace_651421 : CollatzResearch.WordTrace tailWord_651421 prefixEnd_651421 148663147303378242685189 := by
  unfold tailWord_651421
  simp only [CollatzResearch.WordTrace]
  refine ⟨23759275773020445694538117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15839517182013630463025411 23759275773020445694538117)
  ·
    refine ⟨4454864207441333567725897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23759275773020445694538117 4454864207441333567725897)
    ·
      refine ⟨3341148155581000175794423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4454864207441333567725897 3341148155581000175794423)
      ·
        refine ⟨5011722233371500263691635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3341148155581000175794423 5011722233371500263691635)
        ·
          refine ⟨7517583350057250395537453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5011722233371500263691635 7517583350057250395537453)
          ·
            refine ⟨2819093756271468898326545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7517583350057250395537453 2819093756271468898326545)
            ·
              refine ⟨2114320317203601673744909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2819093756271468898326545 2114320317203601673744909)
              ·
                refine ⟨792870118951350627654341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2114320317203601673744909 792870118951350627654341)
                ·
                  refine ⟨148663147303378242685189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 792870118951350627654341 148663147303378242685189)
                  ·
                    rfl

theorem cell21_651421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_651421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651421 prefixEnd_651421 := by exact prefixLift 651421
  have htrace : WordTrace (prefixWord ++ tailWord_651421) baseStart_651421 baseEnd_651421 := by
    simpa [prefixWord, tailWord_651421, baseEnd_651421] using wordTrace_append hprefix tailTrace_651421
  have hstable : (prefixWord ++ tailWord_651421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651421).length < 2 ^ (prefixWord ++ tailWord_651421).sum := by decide
  have hdescent : baseEnd_651421 < baseStart_651421 := by decide
  rcases family_descends (prefixWord ++ tailWord_651421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651449 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 7]
def baseStart_651449 : Nat := 118140960795 + 651449 * 2 ^ 59
def prefixEnd_651449 : Nat := 4983230072969 + 3 ^ 40 * 651449 * 2
def baseEnd_651449 : Nat := 148669537284856416218465

theorem tailTrace_651449 : CollatzResearch.WordTrace tailWord_651449 prefixEnd_651449 148669537284856416218465 := by
  unfold tailWord_651449
  simp only [CollatzResearch.WordTrace]
  refine ⟨23760297016919006476557401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15840198011279337651038267 23760297016919006476557401)
  ·
    refine ⟨17820222762689254857418051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23760297016919006476557401 17820222762689254857418051)
    ·
      refine ⟨26730334144033882286127077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17820222762689254857418051 26730334144033882286127077)
      ·
        refine ⟨5011937652006352928648827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26730334144033882286127077 5011937652006352928648827)
        ·
          refine ⟨7517906478009529392973241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5011937652006352928648827 7517906478009529392973241)
          ·
            refine ⟨5638429858507147044729931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7517906478009529392973241 5638429858507147044729931)
            ·
              refine ⟨8457644787760720567094897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5638429858507147044729931 8457644787760720567094897)
              ·
                refine ⟨6343233590820540425321173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8457644787760720567094897 6343233590820540425321173)
                ·
                  refine ⟨148669537284856416218465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6343233590820540425321173 148669537284856416218465)
                  ·
                    rfl

theorem cell21_651449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_651449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651449 prefixEnd_651449 := by exact prefixLift 651449
  have htrace : WordTrace (prefixWord ++ tailWord_651449) baseStart_651449 baseEnd_651449 := by
    simpa [prefixWord, tailWord_651449, baseEnd_651449] using wordTrace_append hprefix tailTrace_651449
  have hstable : (prefixWord ++ tailWord_651449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651449).length < 2 ^ (prefixWord ++ tailWord_651449).sum := by decide
  have hdescent : baseEnd_651449 < baseStart_651449 := by decide
  rcases family_descends (prefixWord ++ tailWord_651449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651466 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_651466 : Nat := 118140960795 + 651466 * 2 ^ 59
def prefixEnd_651466 : Nat := 4983230072969 + 3 ^ 40 * 651466 * 2
def baseEnd_651466 : Nat := 148673416916468164435097

theorem tailTrace_651466 : CollatzResearch.WordTrace tailWord_651466 prefixEnd_651466 148673416916468164435097 := by
  unfold tailWord_651466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5940229264464354594981563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15840611371904945586617501 5940229264464354594981563)
  ·
    refine ⟨8910343896696531892472345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5940229264464354594981563 8910343896696531892472345)
    ·
      refine ⟨6682757922522398919354259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8910343896696531892472345 6682757922522398919354259)
      ·
        refine ⟨10024136883783598379031389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6682757922522398919354259 10024136883783598379031389)
        ·
          refine ⟨3759051331418849392136771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10024136883783598379031389 3759051331418849392136771)
          ·
            refine ⟨5638576997128274088205157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3759051331418849392136771 5638576997128274088205157)
            ·
              refine ⟨1057233186961551391538467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5638576997128274088205157 1057233186961551391538467)
              ·
                refine ⟨1585849780442327087307701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057233186961551391538467 1585849780442327087307701)
                ·
                  refine ⟨148673416916468164435097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1585849780442327087307701 148673416916468164435097)
                  ·
                    rfl

theorem cell21_651466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_651466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651466 prefixEnd_651466 := by exact prefixLift 651466
  have htrace : WordTrace (prefixWord ++ tailWord_651466) baseStart_651466 baseEnd_651466 := by
    simpa [prefixWord, tailWord_651466, baseEnd_651466] using wordTrace_append hprefix tailTrace_651466
  have hstable : (prefixWord ++ tailWord_651466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651466).length < 2 ^ (prefixWord ++ tailWord_651466).sum := by decide
  have hdescent : baseEnd_651466 < baseStart_651466 := by decide
  rcases family_descends (prefixWord ++ tailWord_651466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651525 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 5]
def baseStart_651525 : Nat := 118140960795 + 651525 * 2 ^ 59
def prefixEnd_651525 : Nat := 4983230072969 + 3 ^ 40 * 651525 * 2
def baseEnd_651525 : Nat := 148686881520297172951643

theorem tailTrace_651525 : CollatzResearch.WordTrace tailWord_651525 prefixEnd_651525 148686881520297172951643 := by
  unfold tailWord_651525
  simp only [CollatzResearch.WordTrace]
  refine ⟨23763068964643671456324029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15842045976429114304216019 23763068964643671456324029)
  ·
    refine ⟨8911150861741376796121511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23763068964643671456324029 8911150861741376796121511)
    ·
      refine ⟨13366726292612065194182267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8911150861741376796121511 13366726292612065194182267)
      ·
        refine ⟨20050089438918097791273401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13366726292612065194182267 20050089438918097791273401)
        ·
          refine ⟨15037567079188573343455051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20050089438918097791273401 15037567079188573343455051)
          ·
            refine ⟨22556350618782860015182577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15037567079188573343455051 22556350618782860015182577)
            ·
              refine ⟨16917262964087145011386933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22556350618782860015182577 16917262964087145011386933)
              ·
                refine ⟨1585993402883169844817525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16917262964087145011386933 1585993402883169844817525)
                ·
                  refine ⟨148686881520297172951643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1585993402883169844817525 148686881520297172951643)
                  ·
                    rfl

theorem cell21_651525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_651525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651525 prefixEnd_651525 := by exact prefixLift 651525
  have htrace : WordTrace (prefixWord ++ tailWord_651525) baseStart_651525 baseEnd_651525 := by
    simpa [prefixWord, tailWord_651525, baseEnd_651525] using wordTrace_append hprefix tailTrace_651525
  have hstable : (prefixWord ++ tailWord_651525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651525).length < 2 ^ (prefixWord ++ tailWord_651525).sum := by decide
  have hdescent : baseEnd_651525 < baseStart_651525 := by decide
  rcases family_descends (prefixWord ++ tailWord_651525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651570 : List Nat := [3, 2, 1, 1, 14]
def baseStart_651570 : Nat := 118140960795 + 651570 * 2 ^ 59
def prefixEnd_651570 : Nat := 4983230072969 + 3 ^ 40 * 651570 * 2
def baseEnd_651570 : Nat := 1835767297943050551871

theorem tailTrace_651570 : CollatzResearch.WordTrace tailWord_651570 prefixEnd_651570 1835767297943050551871 := by
  unfold tailWord_651570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5941177562370161035428041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15843140166320429427808109 5941177562370161035428041)
  ·
    refine ⟨4455883171777620776571031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5941177562370161035428041 4455883171777620776571031)
    ·
      refine ⟨6683824757666431164856547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4455883171777620776571031 6683824757666431164856547)
      ·
        refine ⟨10025737136499646747284821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6683824757666431164856547 10025737136499646747284821)
        ·
          refine ⟨1835767297943050551871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 10025737136499646747284821 1835767297943050551871)
          ·
            rfl

theorem cell21_651570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 14].length) (baseStart_651570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651570 prefixEnd_651570 := by exact prefixLift 651570
  have htrace : WordTrace (prefixWord ++ tailWord_651570) baseStart_651570 baseEnd_651570 := by
    simpa [prefixWord, tailWord_651570, baseEnd_651570] using wordTrace_append hprefix tailTrace_651570
  have hstable : (prefixWord ++ tailWord_651570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651570).length < 2 ^ (prefixWord ++ tailWord_651570).sum := by decide
  have hdescent : baseEnd_651570 < baseStart_651570 := by decide
  rcases family_descends (prefixWord ++ tailWord_651570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651573 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 4]
def baseStart_651573 : Nat := 118140960795 + 651573 * 2 ^ 59
def prefixEnd_651573 : Nat := 4983230072969 + 3 ^ 40 * 651573 * 2
def baseEnd_651573 : Nat := 148697835774259756151545

theorem tailTrace_651573 : CollatzResearch.WordTrace tailWord_651573 prefixEnd_651573 148697835774259756151545 := by
  unfold tailWord_651573
  simp only [CollatzResearch.WordTrace]
  refine ⟨23764819668469775654071373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15843213112313183769380915 23764819668469775654071373)
  ·
    refine ⟨8911807375676165870276765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23764819668469775654071373 8911807375676165870276765)
    ·
      refine ⟨3341927765878562201353787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8911807375676165870276765 3341927765878562201353787)
      ·
        refine ⟨5012891648817843302030681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3341927765878562201353787 5012891648817843302030681)
        ·
          refine ⟨3759668736613382476523011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5012891648817843302030681 3759668736613382476523011)
          ·
            refine ⟨5639503104920073714784517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3759668736613382476523011 5639503104920073714784517)
            ·
              refine ⟨1057406832172513821522097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5639503104920073714784517 1057406832172513821522097)
              ·
                refine ⟨793055124129385366141573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1057406832172513821522097 793055124129385366141573)
                ·
                  refine ⟨148697835774259756151545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 793055124129385366141573 148697835774259756151545)
                  ·
                    rfl

theorem cell21_651573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_651573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651573 prefixEnd_651573 := by exact prefixLift 651573
  have htrace : WordTrace (prefixWord ++ tailWord_651573) baseStart_651573 baseEnd_651573 := by
    simpa [prefixWord, tailWord_651573, baseEnd_651573] using wordTrace_append hprefix tailTrace_651573
  have hstable : (prefixWord ++ tailWord_651573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651573).length < 2 ^ (prefixWord ++ tailWord_651573).sum := by decide
  have hdescent : baseEnd_651573 < baseStart_651573 := by decide
  rcases family_descends (prefixWord ++ tailWord_651573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651601 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 7]
def baseStart_651601 : Nat := 118140960795 + 651601 * 2 ^ 59
def prefixEnd_651601 : Nat := 4983230072969 + 3 ^ 40 * 651601 * 2
def baseEnd_651601 : Nat := 148704225755737929684821

theorem tailTrace_651601 : CollatzResearch.WordTrace tailWord_651601 prefixEnd_651601 148704225755737929684821 := by
  unfold tailWord_651601
  simp only [CollatzResearch.WordTrace]
  refine ⟨23765840912368336436090657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15843893941578890957393771 23765840912368336436090657)
  ·
    refine ⟨17824380684276252327067993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23765840912368336436090657 17824380684276252327067993)
    ·
      refine ⟨13368285513207189245300995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17824380684276252327067993 13368285513207189245300995)
      ·
        refine ⟨20052428269810783867951493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13368285513207189245300995 20052428269810783867951493)
        ·
          refine ⟨3759830300589521975240905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20052428269810783867951493 3759830300589521975240905)
          ·
            refine ⟨2819872725442141481430679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3759830300589521975240905 2819872725442141481430679)
            ·
              refine ⟨4229809088163212222146019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819872725442141481430679 4229809088163212222146019)
              ·
                refine ⟨6344713632244818333219029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4229809088163212222146019 6344713632244818333219029)
                ·
                  refine ⟨148704225755737929684821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6344713632244818333219029 148704225755737929684821)
                  ·
                    rfl

theorem cell21_651601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_651601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651601 prefixEnd_651601 := by exact prefixLift 651601
  have htrace : WordTrace (prefixWord ++ tailWord_651601) baseStart_651601 baseEnd_651601 := by
    simpa [prefixWord, tailWord_651601, baseEnd_651601] using wordTrace_append hprefix tailTrace_651601
  have hstable : (prefixWord ++ tailWord_651601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651601).length < 2 ^ (prefixWord ++ tailWord_651601).sum := by decide
  have hdescent : baseEnd_651601 < baseStart_651601 := by decide
  rcases family_descends (prefixWord ++ tailWord_651601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651604 : List Nat := [2, 4, 1, 1, 2, 3, 3, 5]
def baseStart_651604 : Nat := 118140960795 + 651604 * 2 ^ 59
def prefixEnd_651604 : Nat := 4983230072969 + 3 ^ 40 * 651604 * 2
def baseEnd_651604 : Nat := 49568303465536863711605

theorem tailTrace_651604 : CollatzResearch.WordTrace tailWord_651604 prefixEnd_651604 49568303465536863711605 := by
  unfold tailWord_651604
  simp only [CollatzResearch.WordTrace]
  refine ⟨11882975165678733974224933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15843966887571645298966577 11882975165678733974224933)
  ·
    refine ⟨2228057843564762620167175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11882975165678733974224933 2228057843564762620167175)
    ·
      refine ⟨3342086765347143930250763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228057843564762620167175 3342086765347143930250763)
      ·
        refine ⟨5013130148020715895376145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3342086765347143930250763 5013130148020715895376145)
        ·
          refine ⟨3759847611015536921532109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5013130148020715895376145 3759847611015536921532109)
          ·
            refine ⟨1409942854130826345574541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3759847611015536921532109 1409942854130826345574541)
            ·
              refine ⟨528728570299059879590453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1409942854130826345574541 528728570299059879590453)
              ·
                refine ⟨49568303465536863711605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 528728570299059879590453 49568303465536863711605)
                ·
                  rfl

theorem cell21_651604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_651604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651604 prefixEnd_651604 := by exact prefixLift 651604
  have htrace : WordTrace (prefixWord ++ tailWord_651604) baseStart_651604 baseEnd_651604 := by
    simpa [prefixWord, tailWord_651604, baseEnd_651604] using wordTrace_append hprefix tailTrace_651604
  have hstable : (prefixWord ++ tailWord_651604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651604).length < 2 ^ (prefixWord ++ tailWord_651604).sum := by decide
  have hdescent : baseEnd_651604 < baseStart_651604 := by decide
  rcases family_descends (prefixWord ++ tailWord_651604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651632 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 6]
def baseStart_651632 : Nat := 118140960795 + 651632 * 2 ^ 59
def prefixEnd_651632 : Nat := 4983230072969 + 3 ^ 40 * 651632 * 2
def baseEnd_651632 : Nat := 148711300378088764668091

theorem tailTrace_651632 : CollatzResearch.WordTrace tailWord_651632 prefixEnd_651632 148711300378088764668091 := by
  unfold tailWord_651632
  simp only [CollatzResearch.WordTrace]
  refine ⟨11883485787628014365234575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15844647716837352486979433 11883485787628014365234575)
  ·
    refine ⟨17825228681442021547851863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11883485787628014365234575 17825228681442021547851863)
    ·
      refine ⟨26737843022163032321777795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17825228681442021547851863 26737843022163032321777795)
      ·
        refine ⟨40106764533244548482666693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26737843022163032321777795 40106764533244548482666693)
        ·
          refine ⟨7520018349983352840500005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40106764533244548482666693 7520018349983352840500005)
          ·
            refine ⟨1410003440621878657593751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7520018349983352840500005 1410003440621878657593751)
            ·
              refine ⟨2115005160932817986390627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410003440621878657593751 2115005160932817986390627)
              ·
                refine ⟨3172507741399226979585941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115005160932817986390627 3172507741399226979585941)
                ·
                  refine ⟨148711300378088764668091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3172507741399226979585941 148711300378088764668091)
                  ·
                    rfl

theorem cell21_651632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_651632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651632 prefixEnd_651632 := by exact prefixLift 651632
  have htrace : WordTrace (prefixWord ++ tailWord_651632) baseStart_651632 baseEnd_651632 := by
    simpa [prefixWord, tailWord_651632, baseEnd_651632] using wordTrace_append hprefix tailTrace_651632
  have hstable : (prefixWord ++ tailWord_651632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651632).length < 2 ^ (prefixWord ++ tailWord_651632).sum := by decide
  have hdescent : baseEnd_651632 < baseStart_651632 := by decide
  rcases family_descends (prefixWord ++ tailWord_651632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651722 : List Nat := [3, 1, 2, 1, 2, 2, 1, 9]
def baseStart_651722 : Nat := 118140960795 + 651722 * 2 ^ 59
def prefixEnd_651722 : Nat := 4983230072969 + 3 ^ 40 * 651722 * 2
def baseEnd_651722 : Nat := 49577279868089536055969

theorem tailTrace_651722 : CollatzResearch.WordTrace tailWord_651722 prefixEnd_651722 49577279868089536055969 := by
  unfold tailWord_651722
  simp only [CollatzResearch.WordTrace]
  refine ⟨5942563536232493525311355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15846836096619982734163613 5942563536232493525311355)
  ·
    refine ⟨8913845304348740287967033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5942563536232493525311355 8913845304348740287967033)
    ·
      refine ⟨6685383978261555215975275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8913845304348740287967033 6685383978261555215975275)
      ·
        refine ⟨10028075967392332823962913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6685383978261555215975275 10028075967392332823962913)
        ·
          refine ⟨7521056975544249617972185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10028075967392332823962913 7521056975544249617972185)
          ·
            refine ⟨5640792731658187213479139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7521056975544249617972185 5640792731658187213479139)
            ·
              refine ⟨8461189097487280820218709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5640792731658187213479139 8461189097487280820218709)
              ·
                refine ⟨49577279868089536055969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8461189097487280820218709 49577279868089536055969)
                ·
                  rfl

theorem cell21_651722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_651722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651722 prefixEnd_651722 := by exact prefixLift 651722
  have htrace : WordTrace (prefixWord ++ tailWord_651722) baseStart_651722 baseEnd_651722 := by
    simpa [prefixWord, tailWord_651722, baseEnd_651722] using wordTrace_append hprefix tailTrace_651722
  have hstable : (prefixWord ++ tailWord_651722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651722).length < 2 ^ (prefixWord ++ tailWord_651722).sum := by decide
  have hdescent : baseEnd_651722 < baseStart_651722 := by decide
  rcases family_descends (prefixWord ++ tailWord_651722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651787 : List Nat := [1, 1, 1, 1, 7, 2, 2, 3, 3]
def baseStart_651787 : Nat := 118140960795 + 651787 * 2 ^ 59
def prefixEnd_651787 : Nat := 4983230072969 + 3 ^ 40 * 651787 * 2
def baseEnd_651787 : Nat := 148746673489842939584441

theorem tailTrace_651787 : CollatzResearch.WordTrace tailWord_651787 prefixEnd_651787 148746673489842939584441 := by
  unfold tailWord_651787
  simp only [CollatzResearch.WordTrace]
  refine ⟨23772624889694490202361615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15848416593129660134907743 23772624889694490202361615)
  ·
    refine ⟨35658937334541735303542423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23772624889694490202361615 35658937334541735303542423)
    ·
      refine ⟨53488406001812602955313635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35658937334541735303542423 53488406001812602955313635)
      ·
        refine ⟨80232609002718904432970453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53488406001812602955313635 80232609002718904432970453)
        ·
          refine ⟨1880451773501224322647745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 80232609002718904432970453 1880451773501224322647745)
          ·
            refine ⟨1410338830125918241985809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1880451773501224322647745 1410338830125918241985809)
            ·
              refine ⟨1057754122594438681489357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410338830125918241985809 1057754122594438681489357)
              ·
                refine ⟨396657795972914505558509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1057754122594438681489357 396657795972914505558509)
                ·
                  refine ⟨148746673489842939584441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396657795972914505558509 148746673489842939584441)
                  ·
                    rfl

theorem cell21_651787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 3].length) (baseStart_651787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651787 prefixEnd_651787 := by exact prefixLift 651787
  have htrace : WordTrace (prefixWord ++ tailWord_651787) baseStart_651787 baseEnd_651787 := by
    simpa [prefixWord, tailWord_651787, baseEnd_651787] using wordTrace_append hprefix tailTrace_651787
  have hstable : (prefixWord ++ tailWord_651787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651787).length < 2 ^ (prefixWord ++ tailWord_651787).sum := by decide
  have hdescent : baseEnd_651787 < baseStart_651787 := by decide
  rcases family_descends (prefixWord ++ tailWord_651787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651818 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_651818 : Nat := 118140960795 + 651818 * 2 ^ 59
def prefixEnd_651818 : Nat := 4983230072969 + 3 ^ 40 * 651818 * 2
def baseEnd_651818 : Nat := 148753748112193774567711

theorem tailTrace_651818 : CollatzResearch.WordTrace tailWord_651818 prefixEnd_651818 148753748112193774567711 := by
  unfold tailWord_651818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943438888145545624185027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15849170368388121664493405 5943438888145545624185027)
  ·
    refine ⟨8915158332218318436277541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5943438888145545624185027 8915158332218318436277541)
    ·
      refine ⟨1671592187290934706802039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8915158332218318436277541 1671592187290934706802039)
      ·
        refine ⟨2507388280936402060203059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671592187290934706802039 2507388280936402060203059)
        ·
          refine ⟨3761082421404603090304589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507388280936402060203059 3761082421404603090304589)
          ·
            refine ⟨1410405908026726158864221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3761082421404603090304589 1410405908026726158864221)
            ·
              refine ⟨528902215510022309574083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1410405908026726158864221 528902215510022309574083)
              ·
                refine ⟨793353323265033464361125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528902215510022309574083 793353323265033464361125)
                ·
                  refine ⟨148753748112193774567711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 793353323265033464361125 148753748112193774567711)
                  ·
                    rfl

theorem cell21_651818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_651818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651818 prefixEnd_651818 := by exact prefixLift 651818
  have htrace : WordTrace (prefixWord ++ tailWord_651818) baseStart_651818 baseEnd_651818 := by
    simpa [prefixWord, tailWord_651818, baseEnd_651818] using wordTrace_append hprefix tailTrace_651818
  have hstable : (prefixWord ++ tailWord_651818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651818).length < 2 ^ (prefixWord ++ tailWord_651818).sum := by decide
  have hdescent : baseEnd_651818 < baseStart_651818 := by decide
  rcases family_descends (prefixWord ++ tailWord_651818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651829 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 5]
def baseStart_651829 : Nat := 118140960795 + 651829 * 2 ^ 59
def prefixEnd_651829 : Nat := 4983230072969 + 3 ^ 40 * 651829 * 2
def baseEnd_651829 : Nat := 148756258462060199884355

theorem tailTrace_651829 : CollatzResearch.WordTrace tailWord_651829 prefixEnd_651829 148756258462060199884355 := by
  unfold tailWord_651829
  simp only [CollatzResearch.WordTrace]
  refine ⟨23774156755542331375390541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15849437837028220916927027 23774156755542331375390541)
  ·
    refine ⟨8915308783328374265771453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23774156755542331375390541 8915308783328374265771453)
    ·
      refine ⟨3343240793748140349664295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8915308783328374265771453 3343240793748140349664295)
      ·
        refine ⟨5014861190622210524496443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3343240793748140349664295 5014861190622210524496443)
        ·
          refine ⟨7522291785933315786744665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5014861190622210524496443 7522291785933315786744665)
          ·
            refine ⟨5641718839449986840058499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7522291785933315786744665 5641718839449986840058499)
            ·
              refine ⟨8462578259174980260087749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641718839449986840058499 8462578259174980260087749)
              ·
                refine ⟨1586733423595308798766453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8462578259174980260087749 1586733423595308798766453)
                ·
                  refine ⟨148756258462060199884355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1586733423595308798766453 148756258462060199884355)
                  ·
                    rfl

theorem cell21_651829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_651829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651829 prefixEnd_651829 := by exact prefixLift 651829
  have htrace : WordTrace (prefixWord ++ tailWord_651829) baseStart_651829 baseEnd_651829 := by
    simpa [prefixWord, tailWord_651829, baseEnd_651829] using wordTrace_append hprefix tailTrace_651829
  have hstable : (prefixWord ++ tailWord_651829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651829).length < 2 ^ (prefixWord ++ tailWord_651829).sum := by decide
  have hdescent : baseEnd_651829 < baseStart_651829 := by decide
  rcases family_descends (prefixWord ++ tailWord_651829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651838 : List Nat := [4, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_651838 : Nat := 118140960795 + 651838 * 2 ^ 59
def prefixEnd_651838 : Nat := 4983230072969 + 3 ^ 40 * 651838 * 2
def baseEnd_651838 : Nat := 148758312384678184234337

theorem tailTrace_651838 : CollatzResearch.WordTrace tailWord_651838 prefixEnd_651838 148758312384678184234337 := by
  unfold tailWord_651838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971810626563715739058521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15849656675006483941645445 2971810626563715739058521)
  ·
    refine ⟨2228857969922786804293891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2971810626563715739058521 2228857969922786804293891)
    ·
      refine ⟨3343286954884180206440837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228857969922786804293891 3343286954884180206440837)
      ·
        refine ⟨626866304040783788707657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3343286954884180206440837 626866304040783788707657)
        ·
          refine ⟨470149728030587841530743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626866304040783788707657 470149728030587841530743)
          ·
            refine ⟨705224592045881762296115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470149728030587841530743 705224592045881762296115)
            ·
              refine ⟨1057836888068822643444173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705224592045881762296115 1057836888068822643444173)
              ·
                refine ⟨396688833025808491291565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1057836888068822643444173 396688833025808491291565)
                ·
                  refine ⟨148758312384678184234337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396688833025808491291565 148758312384678184234337)
                  ·
                    rfl

theorem cell21_651838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_651838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651838 prefixEnd_651838 := by exact prefixLift 651838
  have htrace : WordTrace (prefixWord ++ tailWord_651838) baseStart_651838 baseEnd_651838 := by
    simpa [prefixWord, tailWord_651838, baseEnd_651838] using wordTrace_append hprefix tailTrace_651838
  have hstable : (prefixWord ++ tailWord_651838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651838).length < 2 ^ (prefixWord ++ tailWord_651838).sum := by decide
  have hdescent : baseEnd_651838 < baseStart_651838 := by decide
  rcases family_descends (prefixWord ++ tailWord_651838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651860 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_651860 : Nat := 118140960795 + 651860 * 2 ^ 59
def prefixEnd_651860 : Nat := 4983230072969 + 3 ^ 40 * 651860 * 2
def baseEnd_651860 : Nat := 148763333084411034867625

theorem tailTrace_651860 : CollatzResearch.WordTrace tailWord_651860 prefixEnd_651860 148763333084411034867625 := by
  unfold tailWord_651860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11887643709215011834884517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15850191612286682446512689 11887643709215011834884517)
  ·
    refine ⟨2228933195477814719040847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11887643709215011834884517 2228933195477814719040847)
    ·
      refine ⟨3343399793216722078561271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228933195477814719040847 3343399793216722078561271)
      ·
        refine ⟨5015099689825083117841907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3343399793216722078561271 5015099689825083117841907)
        ·
          refine ⟨7522649534737624676762861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5015099689825083117841907 7522649534737624676762861)
          ·
            refine ⟨2820993575526609253786073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7522649534737624676762861 2820993575526609253786073)
            ·
              refine ⟨2115745181644956940339555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2820993575526609253786073 2115745181644956940339555)
              ·
                refine ⟨3173617772467435410509333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115745181644956940339555 3173617772467435410509333)
                ·
                  refine ⟨148763333084411034867625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3173617772467435410509333 148763333084411034867625)
                  ·
                    rfl

theorem cell21_651860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_651860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651860 prefixEnd_651860 := by exact prefixLift 651860
  have htrace : WordTrace (prefixWord ++ tailWord_651860) baseStart_651860 baseEnd_651860 := by
    simpa [prefixWord, tailWord_651860, baseEnd_651860] using wordTrace_append hprefix tailTrace_651860
  have hstable : (prefixWord ++ tailWord_651860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651860).length < 2 ^ (prefixWord ++ tailWord_651860).sum := by decide
  have hdescent : baseEnd_651860 < baseStart_651860 := by decide
  rcases family_descends (prefixWord ++ tailWord_651860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651863 : List Nat := [1, 1, 3, 2, 2, 2, 5, 2, 3]
def baseStart_651863 : Nat := 118140960795 + 651863 * 2 ^ 59
def prefixEnd_651863 : Nat := 4983230072969 + 3 ^ 40 * 651863 * 2
def baseEnd_651863 : Nat := 148764017725283696317619

theorem tailTrace_651863 : CollatzResearch.WordTrace tailWord_651863 prefixEnd_651863 148764017725283696317619 := by
  unfold tailWord_651863
  simp only [CollatzResearch.WordTrace]
  refine ⟨23775396837419155182128243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15850264558279436788085495 23775396837419155182128243)
  ·
    refine ⟨35663095256128732773192365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23775396837419155182128243 35663095256128732773192365)
    ·
      refine ⟨13373660721048274789947137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35663095256128732773192365 13373660721048274789947137)
      ·
        refine ⟨10030245540786206092460353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13373660721048274789947137 10030245540786206092460353)
        ·
          refine ⟨7522684155589654569345265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10030245540786206092460353 7522684155589654569345265)
          ·
            refine ⟨5642013116692240927008949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7522684155589654569345265 5642013116692240927008949)
            ·
              refine ⟨528938729689897586907089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5642013116692240927008949 528938729689897586907089)
              ·
                refine ⟨396704047267423190180317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528938729689897586907089 396704047267423190180317)
                ·
                  refine ⟨148764017725283696317619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396704047267423190180317 148764017725283696317619)
                  ·
                    rfl

theorem cell21_651863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 3].length) (baseStart_651863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651863 prefixEnd_651863 := by exact prefixLift 651863
  have htrace : WordTrace (prefixWord ++ tailWord_651863) baseStart_651863 baseEnd_651863 := by
    simpa [prefixWord, tailWord_651863, baseEnd_651863] using wordTrace_append hprefix tailTrace_651863
  have hstable : (prefixWord ++ tailWord_651863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651863).length < 2 ^ (prefixWord ++ tailWord_651863).sum := by decide
  have hdescent : baseEnd_651863 < baseStart_651863 := by decide
  rcases family_descends (prefixWord ++ tailWord_651863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_651877 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 4]
def baseStart_651877 : Nat := 118140960795 + 651877 * 2 ^ 59
def prefixEnd_651877 : Nat := 4983230072969 + 3 ^ 40 * 651877 * 2
def baseEnd_651877 : Nat := 148767212716022783084257

theorem tailTrace_651877 : CollatzResearch.WordTrace tailWord_651877 prefixEnd_651877 148767212716022783084257 := by
  unfold tailWord_651877
  simp only [CollatzResearch.WordTrace]
  refine ⟨23775907459368435573137885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15850604972912290382091923 23775907459368435573137885)
  ·
    refine ⟨8915965297263163339926707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23775907459368435573137885 8915965297263163339926707)
    ·
      refine ⟨13373947945894745009890061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8915965297263163339926707 13373947945894745009890061)
      ·
        refine ⟨5015230479710529378708773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13373947945894745009890061 5015230479710529378708773)
        ·
          refine ⟨940355714945724258507895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5015230479710529378708773 940355714945724258507895)
          ·
            refine ⟨1410533572418586387761843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940355714945724258507895 1410533572418586387761843)
            ·
              refine ⟨2115800358627879581642765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410533572418586387761843 2115800358627879581642765)
              ·
                refine ⟨793425134485454843116037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2115800358627879581642765 793425134485454843116037)
                ·
                  refine ⟨148767212716022783084257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 793425134485454843116037 148767212716022783084257)
                  ·
                    rfl

theorem cell21_651877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_651877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_651877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_651877 prefixEnd_651877 := by exact prefixLift 651877
  have htrace : WordTrace (prefixWord ++ tailWord_651877) baseStart_651877 baseEnd_651877 := by
    simpa [prefixWord, tailWord_651877, baseEnd_651877] using wordTrace_append hprefix tailTrace_651877
  have hstable : (prefixWord ++ tailWord_651877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_651877).length < 2 ^ (prefixWord ++ tailWord_651877).sum := by decide
  have hdescent : baseEnd_651877 < baseStart_651877 := by decide
  rcases family_descends (prefixWord ++ tailWord_651877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652015 : List Nat := [1, 1, 2, 1, 5, 4, 1, 3, 3]
def baseStart_652015 : Nat := 118140960795 + 652015 * 2 ^ 59
def prefixEnd_652015 : Nat := 4983230072969 + 3 ^ 40 * 652015 * 2
def baseEnd_652015 : Nat := 148798706196165209783975

theorem tailTrace_652015 : CollatzResearch.WordTrace tailWord_652015 prefixEnd_652015 148798706196165209783975 := by
  unfold tailWord_652015
  simp only [CollatzResearch.WordTrace]
  refine ⟨23780940732868485141661499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15853960488578990094440999 23780940732868485141661499)
  ·
    refine ⟨35671411099302727712492249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23780940732868485141661499 35671411099302727712492249)
    ·
      refine ⟨26753558324477045784369187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35671411099302727712492249 26753558324477045784369187)
      ·
        refine ⟨40130337486715568676553781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26753558324477045784369187 40130337486715568676553781)
        ·
          refine ⟨3762219139379584563426917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40130337486715568676553781 3762219139379584563426917)
          ·
            refine ⟨705416088633672105642547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3762219139379584563426917 705416088633672105642547)
            ·
              refine ⟨1058124132950508158463821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705416088633672105642547 1058124132950508158463821)
              ·
                refine ⟨396796549856440559423933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1058124132950508158463821 396796549856440559423933)
                ·
                  refine ⟨148798706196165209783975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396796549856440559423933 148798706196165209783975)
                  ·
                    rfl

theorem cell21_652015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 3].length) (baseStart_652015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652015 prefixEnd_652015 := by exact prefixLift 652015
  have htrace : WordTrace (prefixWord ++ tailWord_652015) baseStart_652015 baseEnd_652015 := by
    simpa [prefixWord, tailWord_652015, baseEnd_652015] using wordTrace_append hprefix tailTrace_652015
  have hstable : (prefixWord ++ tailWord_652015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652015).length < 2 ^ (prefixWord ++ tailWord_652015).sum := by decide
  have hdescent : baseEnd_652015 < baseStart_652015 := by decide
  rcases family_descends (prefixWord ++ tailWord_652015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652088 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 4]
def baseStart_652088 : Nat := 118140960795 + 652088 * 2 ^ 59
def prefixEnd_652088 : Nat := 4983230072969 + 3 ^ 40 * 652088 * 2
def baseEnd_652088 : Nat := 148815365790733305067159

theorem tailTrace_652088 : CollatzResearch.WordTrace tailWord_652088 prefixEnd_652088 148815365790733305067159 := by
  unfold tailWord_652088
  simp only [CollatzResearch.WordTrace]
  refine ⟨11891801630802009304534459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15855735507736012406045945 11891801630802009304534459)
  ·
    refine ⟨17837702446203013956801689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11891801630802009304534459 17837702446203013956801689)
    ·
      refine ⟨13378276834652260467601267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17837702446203013956801689 13378276834652260467601267)
      ·
        refine ⟨20067415251978390701401901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13378276834652260467601267 20067415251978390701401901)
        ·
          refine ⟨7525280719491896513025713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20067415251978390701401901 7525280719491896513025713)
          ·
            refine ⟨5643960539618922384769285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7525280719491896513025713 5643960539618922384769285)
            ·
              refine ⟨1058242601178547947144241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5643960539618922384769285 1058242601178547947144241)
              ·
                refine ⟨793681950883910960358181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058242601178547947144241 793681950883910960358181)
                ·
                  refine ⟨148815365790733305067159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 793681950883910960358181 148815365790733305067159)
                  ·
                    rfl

theorem cell21_652088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_652088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652088 prefixEnd_652088 := by exact prefixLift 652088
  have htrace : WordTrace (prefixWord ++ tailWord_652088) baseStart_652088 baseEnd_652088 := by
    simpa [prefixWord, tailWord_652088, baseEnd_652088] using wordTrace_append hprefix tailTrace_652088
  have hstable : (prefixWord ++ tailWord_652088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652088).length < 2 ^ (prefixWord ++ tailWord_652088).sum := by decide
  have hdescent : baseEnd_652088 < baseStart_652088 := by decide
  rcases family_descends (prefixWord ++ tailWord_652088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652119 : List Nat := [1, 1, 3, 2, 4, 2, 3, 5]
def baseStart_652119 : Nat := 118140960795 + 652119 * 2 ^ 59
def prefixEnd_652119 : Nat := 4983230072969 + 3 ^ 40 * 652119 * 2
def baseEnd_652119 : Nat := 49607480137694713350143

theorem tailTrace_652119 : CollatzResearch.WordTrace tailWord_652119 prefixEnd_652119 49607480137694713350143 := by
  unfold tailWord_652119
  simp only [CollatzResearch.WordTrace]
  refine ⟨23784733924491710903447411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15856489282994473935631607 23784733924491710903447411)
  ·
    refine ⟨35677100886737566355171117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23784733924491710903447411 35677100886737566355171117)
    ·
      refine ⟨13378912832526587383189169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35677100886737566355171117 13378912832526587383189169)
      ·
        refine ⟨10034184624394940537391877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13378912832526587383189169 10034184624394940537391877)
        ·
          refine ⟨1881409617074051350760977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10034184624394940537391877 1881409617074051350760977)
          ·
            refine ⟨1411057212805538513070733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1881409617074051350760977 1411057212805538513070733)
            ·
              refine ⟨529146454802076942401525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1411057212805538513070733 529146454802076942401525)
              ·
                refine ⟨49607480137694713350143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 529146454802076942401525 49607480137694713350143)
                ·
                  rfl

theorem cell21_652119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 5].length) (baseStart_652119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652119 prefixEnd_652119 := by exact prefixLift 652119
  have htrace : WordTrace (prefixWord ++ tailWord_652119) baseStart_652119 baseEnd_652119 := by
    simpa [prefixWord, tailWord_652119, baseEnd_652119] using wordTrace_append hprefix tailTrace_652119
  have hstable : (prefixWord ++ tailWord_652119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652119).length < 2 ^ (prefixWord ++ tailWord_652119).sum := by decide
  have hdescent : baseEnd_652119 < baseStart_652119 := by decide
  rcases family_descends (prefixWord ++ tailWord_652119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652150 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_652150 : Nat := 118140960795 + 652150 * 2 ^ 59
def prefixEnd_652150 : Nat := 4983230072969 + 3 ^ 40 * 652150 * 2
def baseEnd_652150 : Nat := 148829515035434975033699

theorem tailTrace_652150 : CollatzResearch.WordTrace tailWord_652150 prefixEnd_652150 148829515035434975033699 := by
  unfold tailWord_652150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486616536711212699864119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15857243058252935465217269 1486616536711212699864119)
  ·
    refine ⟨2229924805066819049796179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1486616536711212699864119 2229924805066819049796179)
    ·
      refine ⟨3344887207600228574694269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2229924805066819049796179 3344887207600228574694269)
      ·
        refine ⟨1254332702850085715510351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3344887207600228574694269 1254332702850085715510351)
        ·
          refine ⟨1881499054275128573265527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254332702850085715510351 1881499054275128573265527)
          ·
            refine ⟨2822248581412692859898291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881499054275128573265527 2822248581412692859898291)
            ·
              refine ⟨4233372872119039289847437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822248581412692859898291 4233372872119039289847437)
              ·
                refine ⟨1587514827044639733692789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4233372872119039289847437 1587514827044639733692789)
                ·
                  refine ⟨148829515035434975033699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1587514827044639733692789 148829515035434975033699)
                  ·
                    rfl

theorem cell21_652150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_652150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652150 prefixEnd_652150 := by exact prefixLift 652150
  have htrace : WordTrace (prefixWord ++ tailWord_652150) baseStart_652150 baseEnd_652150 := by
    simpa [prefixWord, tailWord_652150, baseEnd_652150] using wordTrace_append hprefix tailTrace_652150
  have hstable : (prefixWord ++ tailWord_652150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652150).length < 2 ^ (prefixWord ++ tailWord_652150).sum := by decide
  have hdescent : baseEnd_652150 < baseStart_652150 := by decide
  rcases family_descends (prefixWord ++ tailWord_652150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652192 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_652192 : Nat := 118140960795 + 652192 * 2 ^ 59
def prefixEnd_652192 : Nat := 4983230072969 + 3 ^ 40 * 652192 * 2
def baseEnd_652192 : Nat := 148839100007652235333613

theorem tailTrace_652192 : CollatzResearch.WordTrace tailWord_652192 prefixEnd_652192 148839100007652235333613 := by
  unfold tailWord_652192
  simp only [CollatzResearch.WordTrace]
  refine ⟨11893698226613622185427415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15858264302151496247236553 11893698226613622185427415)
  ·
    refine ⟨17840547339920433278141123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11893698226613622185427415 17840547339920433278141123)
    ·
      refine ⟨26760821009880649917211685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17840547339920433278141123 26760821009880649917211685)
      ·
        refine ⟨5017653939352621859477191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26760821009880649917211685 5017653939352621859477191)
        ·
          refine ⟨7526480909028932789215787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5017653939352621859477191 7526480909028932789215787)
          ·
            refine ⟨11289721363543399183823681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7526480909028932789215787 11289721363543399183823681)
            ·
              refine ⟨8467291022657549387867761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11289721363543399183823681 8467291022657549387867761)
              ·
                refine ⟨6350468266993162040900821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8467291022657549387867761 6350468266993162040900821)
                ·
                  refine ⟨148839100007652235333613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6350468266993162040900821 148839100007652235333613)
                  ·
                    rfl

theorem cell21_652192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_652192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652192 prefixEnd_652192 := by exact prefixLift 652192
  have htrace : WordTrace (prefixWord ++ tailWord_652192) baseStart_652192 baseEnd_652192 := by
    simpa [prefixWord, tailWord_652192, baseEnd_652192] using wordTrace_append hprefix tailTrace_652192
  have hstable : (prefixWord ++ tailWord_652192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652192).length < 2 ^ (prefixWord ++ tailWord_652192).sum := by decide
  have hdescent : baseEnd_652192 < baseStart_652192 := by decide
  rcases family_descends (prefixWord ++ tailWord_652192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652212 : List Nat := [2, 5, 2, 1, 1, 2, 2, 6]
def baseStart_652212 : Nat := 118140960795 + 652212 * 2 ^ 59
def prefixEnd_652212 : Nat := 4983230072969 + 3 ^ 40 * 652212 * 2
def baseEnd_652212 : Nat := 49614554760045548333413

theorem tailTrace_652212 : CollatzResearch.WordTrace tailWord_652212 prefixEnd_652212 49614554760045548333413 := by
  unfold tailWord_652212
  simp only [CollatzResearch.WordTrace]
  refine ⟨11894062956577393893291445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15858750608769858524388593 11894062956577393893291445)
  ·
    refine ⟨1115068402179130677496073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11894062956577393893291445 1115068402179130677496073)
    ·
      refine ⟨836301301634348008122055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1115068402179130677496073 836301301634348008122055)
      ·
        refine ⟨1254451952451522012183083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836301301634348008122055 1254451952451522012183083)
        ·
          refine ⟨1881677928677283018274625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254451952451522012183083 1881677928677283018274625)
          ·
            refine ⟨1411258446507962263705969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1881677928677283018274625 1411258446507962263705969)
            ·
              refine ⟨1058443834880971697779477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1411258446507962263705969 1058443834880971697779477)
              ·
                refine ⟨49614554760045548333413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1058443834880971697779477 49614554760045548333413)
                ·
                  rfl

theorem cell21_652212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_652212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652212 prefixEnd_652212 := by exact prefixLift 652212
  have htrace : WordTrace (prefixWord ++ tailWord_652212) baseStart_652212 baseEnd_652212 := by
    simpa [prefixWord, tailWord_652212, baseEnd_652212] using wordTrace_append hprefix tailTrace_652212
  have hstable : (prefixWord ++ tailWord_652212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652212).length < 2 ^ (prefixWord ++ tailWord_652212).sum := by decide
  have hdescent : baseEnd_652212 < baseStart_652212 := by decide
  rcases family_descends (prefixWord ++ tailWord_652212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652302 : List Nat := [4, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_652302 : Nat := 118140960795 + 652302 * 2 ^ 59
def prefixEnd_652302 : Nat := 4983230072969 + 3 ^ 40 * 652302 * 2
def baseEnd_652302 : Nat := 148864203506316488500055

theorem tailTrace_652302 : CollatzResearch.WordTrace tailWord_652302 prefixEnd_652302 148864203506316488500055 := by
  unfold tailWord_652302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2973926060353591644669895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15860938988552488771572773 2973926060353591644669895)
  ·
    refine ⟨4460889090530387467004843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2973926060353591644669895 4460889090530387467004843)
    ·
      refine ⟨6691333635795581200507265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4460889090530387467004843 6691333635795581200507265)
      ·
        refine ⟨5018500226846685900380449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6691333635795581200507265 5018500226846685900380449)
        ·
          refine ⟨3763875170135014425285337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5018500226846685900380449 3763875170135014425285337)
          ·
            refine ⟨2822906377601260818964003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3763875170135014425285337 2822906377601260818964003)
            ·
              refine ⟨4234359566401891228446005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822906377601260818964003 4234359566401891228446005)
              ·
                refine ⟨396971209350177302666813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4234359566401891228446005 396971209350177302666813)
                ·
                  refine ⟨148864203506316488500055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396971209350177302666813 148864203506316488500055)
                  ·
                    rfl

theorem cell21_652302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_652302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652302 prefixEnd_652302 := by exact prefixLift 652302
  have htrace : WordTrace (prefixWord ++ tailWord_652302) baseStart_652302 baseEnd_652302 := by
    simpa [prefixWord, tailWord_652302, baseEnd_652302] using wordTrace_append hprefix tailTrace_652302
  have hstable : (prefixWord ++ tailWord_652302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652302).length < 2 ^ (prefixWord ++ tailWord_652302).sum := by decide
  have hdescent : baseEnd_652302 < baseStart_652302 := by decide
  rcases family_descends (prefixWord ++ tailWord_652302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652316 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 6]
def baseStart_652316 : Nat := 118140960795 + 652316 * 2 ^ 59
def prefixEnd_652316 : Nat := 4983230072969 + 3 ^ 40 * 652316 * 2
def baseEnd_652316 : Nat := 148867398497055575266693

theorem tailTrace_652316 : CollatzResearch.WordTrace tailWord_652316 prefixEnd_652316 148867398497055575266693 := by
  unfold tailWord_652316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11895959552389006774184401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15861279403185342365579201 11895959552389006774184401)
  ·
    refine ⟨8921969664291755080638301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11895959552389006774184401 8921969664291755080638301)
    ·
      refine ⟨3345738624109408155239363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8921969664291755080638301 3345738624109408155239363)
      ·
        refine ⟨5018607936164112232859045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3345738624109408155239363 5018607936164112232859045)
        ·
          refine ⟨940988988030771043661071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5018607936164112232859045 940988988030771043661071)
          ·
            refine ⟨1411483482046156565491607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940988988030771043661071 1411483482046156565491607)
            ·
              refine ⟨2117225223069234848237411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411483482046156565491607 2117225223069234848237411)
              ·
                refine ⟨3175837834603852272356117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117225223069234848237411 3175837834603852272356117)
                ·
                  refine ⟨148867398497055575266693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3175837834603852272356117 148867398497055575266693)
                  ·
                    rfl

theorem cell21_652316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_652316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652316 prefixEnd_652316 := by exact prefixLift 652316
  have htrace : WordTrace (prefixWord ++ tailWord_652316) baseStart_652316 baseEnd_652316 := by
    simpa [prefixWord, tailWord_652316, baseEnd_652316] using wordTrace_append hprefix tailTrace_652316
  have hstable : (prefixWord ++ tailWord_652316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652316).length < 2 ^ (prefixWord ++ tailWord_652316).sum := by decide
  have hdescent : baseEnd_652316 < baseStart_652316 := by decide
  rcases family_descends (prefixWord ++ tailWord_652316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652361 : List Nat := [1, 2, 1, 1, 2, 2, 2, 7, 3]
def baseStart_652361 : Nat := 118140960795 + 652361 * 2 ^ 59
def prefixEnd_652361 : Nat := 4983230072969 + 3 ^ 40 * 652361 * 2
def baseEnd_652361 : Nat := 148877668110145497016601

theorem tailTrace_652361 : CollatzResearch.WordTrace tailWord_652361 prefixEnd_652361 148877668110145497016601 := by
  unfold tailWord_652361
  simp only [CollatzResearch.WordTrace]
  refine ⟨23793560389614986233756937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15862373593076657489171291 23793560389614986233756937)
  ·
    refine ⟨17845170292211239675317703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23793560389614986233756937 17845170292211239675317703)
    ·
      refine ⟨26767755438316859512976555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17845170292211239675317703 26767755438316859512976555)
      ·
        refine ⟨40151633157475289269464833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26767755438316859512976555 40151633157475289269464833)
        ·
          refine ⟨30113724868106466952098625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40151633157475289269464833 30113724868106466952098625)
          ·
            refine ⟨22585293651079850214073969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30113724868106466952098625 22585293651079850214073969)
            ·
              refine ⟨16938970238309887660555477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22585293651079850214073969 16938970238309887660555477)
              ·
                refine ⟨397007114960387992044269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16938970238309887660555477 397007114960387992044269)
                ·
                  refine ⟨148877668110145497016601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397007114960387992044269 148877668110145497016601)
                  ·
                    rfl

theorem cell21_652361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 3].length) (baseStart_652361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652361 prefixEnd_652361 := by exact prefixLift 652361
  have htrace : WordTrace (prefixWord ++ tailWord_652361) baseStart_652361 baseEnd_652361 := by
    simpa [prefixWord, tailWord_652361, baseEnd_652361] using wordTrace_append hprefix tailTrace_652361
  have hstable : (prefixWord ++ tailWord_652361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652361).length < 2 ^ (prefixWord ++ tailWord_652361).sum := by decide
  have hdescent : baseEnd_652361 < baseStart_652361 := by decide
  rcases family_descends (prefixWord ++ tailWord_652361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652375 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 4]
def baseStart_652375 : Nat := 118140960795 + 652375 * 2 ^ 59
def prefixEnd_652375 : Nat := 4983230072969 + 3 ^ 40 * 652375 * 2
def baseEnd_652375 : Nat := 148880863100884583783239

theorem tailTrace_652375 : CollatzResearch.WordTrace tailWord_652375 prefixEnd_652375 148880863100884583783239 := by
  unfold tailWord_652375
  simp only [CollatzResearch.WordTrace]
  refine ⟨23794071011564266624766579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15862714007709511083177719 23794071011564266624766579)
  ·
    refine ⟨35691106517346399937149869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23794071011564266624766579 35691106517346399937149869)
    ·
      refine ⟨13384164944004899976431201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35691106517346399937149869 13384164944004899976431201)
      ·
        refine ⟨10038123708003674982323401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13384164944004899976431201 10038123708003674982323401)
        ·
          refine ⟨7528592781002756236742551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10038123708003674982323401 7528592781002756236742551)
          ·
            refine ⟨11292889171504134355113827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7528592781002756236742551 11292889171504134355113827)
            ·
              refine ⟨16939333757256201532670741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11292889171504134355113827 16939333757256201532670741)
              ·
                refine ⟨794031269871384446843941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16939333757256201532670741 794031269871384446843941)
                ·
                  refine ⟨148880863100884583783239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 794031269871384446843941 148880863100884583783239)
                  ·
                    rfl

theorem cell21_652375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 4].length) (baseStart_652375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652375 prefixEnd_652375 := by exact prefixLift 652375
  have htrace : WordTrace (prefixWord ++ tailWord_652375) baseStart_652375 baseEnd_652375 := by
    simpa [prefixWord, tailWord_652375, baseEnd_652375] using wordTrace_append hprefix tailTrace_652375
  have hstable : (prefixWord ++ tailWord_652375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652375).length < 2 ^ (prefixWord ++ tailWord_652375).sum := by decide
  have hdescent : baseEnd_652375 < baseStart_652375 := by decide
  rcases family_descends (prefixWord ++ tailWord_652375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652406 : List Nat := [5, 1, 1, 2, 1, 1, 1, 9]
def baseStart_652406 : Nat := 118140960795 + 652406 * 2 ^ 59
def prefixEnd_652406 : Nat := 4983230072969 + 3 ^ 40 * 652406 * 2
def baseEnd_652406 : Nat := 49629312574411806255503

theorem tailTrace_652406 : CollatzResearch.WordTrace tailWord_652406 prefixEnd_652406 49629312574411806255503 := by
  unfold tailWord_652406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487200104653247432446567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15863467782967972612763381 1487200104653247432446567)
  ·
    refine ⟨2230800156979871148669851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1487200104653247432446567 2230800156979871148669851)
    ·
      refine ⟨3346200235469806723004777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2230800156979871148669851 3346200235469806723004777)
      ·
        refine ⟨2509650176602355042253583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3346200235469806723004777 2509650176602355042253583)
        ·
          refine ⟨3764475264903532563380375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509650176602355042253583 3764475264903532563380375)
          ·
            refine ⟨5646712897355298845070563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764475264903532563380375 5646712897355298845070563)
            ·
              refine ⟨8470069346032948267605845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5646712897355298845070563 8470069346032948267605845)
              ·
                refine ⟨49629312574411806255503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8470069346032948267605845 49629312574411806255503)
                ·
                  rfl

theorem cell21_652406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_652406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652406 prefixEnd_652406 := by exact prefixLift 652406
  have htrace : WordTrace (prefixWord ++ tailWord_652406) baseStart_652406 baseEnd_652406 := by
    simpa [prefixWord, tailWord_652406, baseEnd_652406] using wordTrace_append hprefix tailTrace_652406
  have hstable : (prefixWord ++ tailWord_652406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652406).length < 2 ^ (prefixWord ++ tailWord_652406).sum := by decide
  have hdescent : baseEnd_652406 < baseStart_652406 := by decide
  rcases family_descends (prefixWord ++ tailWord_652406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652558 : List Nat := [4, 1, 1, 2, 1, 4, 2, 6]
def baseStart_652558 : Nat := 118140960795 + 652558 * 2 ^ 59
def prefixEnd_652558 : Nat := 4983230072969 + 3 ^ 40 * 652558 * 2
def baseEnd_652558 : Nat := 49640875398038977410955

theorem tailTrace_652558 : CollatzResearch.WordTrace tailWord_652558 prefixEnd_652558 49640875398038977410955 := by
  unfold tailWord_652558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2975093196237661109834791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15867163713267525919118885 2975093196237661109834791)
  ·
    refine ⟨4462639794356491664752187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2975093196237661109834791 4462639794356491664752187)
    ·
      refine ⟨6693959691534737497128281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4462639794356491664752187 6693959691534737497128281)
      ·
        refine ⟨5020469768651053122846211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6693959691534737497128281 5020469768651053122846211)
        ·
          refine ⟨7530704652976579684269317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5020469768651053122846211 7530704652976579684269317)
          ·
            refine ⟨1412007122433108690800497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7530704652976579684269317 1412007122433108690800497)
            ·
              refine ⟨1059005341824831518100373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1412007122433108690800497 1059005341824831518100373)
              ·
                refine ⟨49640875398038977410955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1059005341824831518100373 49640875398038977410955)
                ·
                  rfl

theorem cell21_652558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_652558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652558 prefixEnd_652558 := by exact prefixLift 652558
  have htrace : WordTrace (prefixWord ++ tailWord_652558) baseStart_652558 baseEnd_652558 := by
    simpa [prefixWord, tailWord_652558, baseEnd_652558] using wordTrace_append hprefix tailTrace_652558
  have hstable : (prefixWord ++ tailWord_652558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652558).length < 2 ^ (prefixWord ++ tailWord_652558).sum := by decide
  have hdescent : baseEnd_652558 < baseStart_652558 := by decide
  rcases family_descends (prefixWord ++ tailWord_652558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652572 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_652572 : Nat := 118140960795 + 652572 * 2 ^ 59
def prefixEnd_652572 : Nat := 4983230072969 + 3 ^ 40 * 652572 * 2
def baseEnd_652572 : Nat := 148925821184856018999503

theorem tailTrace_652572 : CollatzResearch.WordTrace tailWord_652572 prefixEnd_652572 148925821184856018999503 := by
  unfold tailWord_652572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11900628095925284634843985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15867504127900379513125313 11900628095925284634843985)
  ·
    refine ⟨8925471071943963476132989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11900628095925284634843985 8925471071943963476132989)
    ·
      refine ⟨3347051651978986303549871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8925471071943963476132989 3347051651978986303549871)
      ·
        refine ⟨5020577477968479455324807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3347051651978986303549871 5020577477968479455324807)
        ·
          refine ⟨7530866216952719182987211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5020577477968479455324807 7530866216952719182987211)
          ·
            refine ⟨11296299325429078774480817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7530866216952719182987211 11296299325429078774480817)
            ·
              refine ⟨8472224494071809080860613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11296299325429078774480817 8472224494071809080860613)
              ·
                refine ⟨1588542092638464202661365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8472224494071809080860613 1588542092638464202661365)
                ·
                  refine ⟨148925821184856018999503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1588542092638464202661365 148925821184856018999503)
                  ·
                    rfl

theorem cell21_652572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_652572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652572 prefixEnd_652572 := by exact prefixLift 652572
  have htrace : WordTrace (prefixWord ++ tailWord_652572) baseStart_652572 baseEnd_652572 := by
    simpa [prefixWord, tailWord_652572, baseEnd_652572] using wordTrace_append hprefix tailTrace_652572
  have hstable : (prefixWord ++ tailWord_652572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652572).length < 2 ^ (prefixWord ++ tailWord_652572).sum := by decide
  have hdescent : baseEnd_652572 < baseStart_652572 := by decide
  rcases family_descends (prefixWord ++ tailWord_652572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652598 : List Nat := [5, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_652598 : Nat := 118140960795 + 652598 * 2 ^ 59
def prefixEnd_652598 : Nat := 4983230072969 + 3 ^ 40 * 652598 * 2
def baseEnd_652598 : Nat := 148931754739085751566117

theorem tailTrace_652598 : CollatzResearch.WordTrace tailWord_652598 prefixEnd_652598 148931754739085751566117 := by
  unfold tailWord_652598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487637780609773481883403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15868136326504250473422965 1487637780609773481883403)
  ·
    refine ⟨2231456670914660222825105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1487637780609773481883403 2231456670914660222825105)
    ·
      refine ⟨1673592503185995167118829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2231456670914660222825105 1673592503185995167118829)
      ·
        refine ⟨627597188694748187669561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1673592503185995167118829 627597188694748187669561)
        ·
          refine ⟨470697891521061140752171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 627597188694748187669561 470697891521061140752171)
          ·
            refine ⟨706046837281591711128257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470697891521061140752171 706046837281591711128257)
            ·
              refine ⟨529535127961193783346193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706046837281591711128257 529535127961193783346193)
              ·
                refine ⟨397151345970895337509645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529535127961193783346193 397151345970895337509645)
                ·
                  refine ⟨148931754739085751566117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397151345970895337509645 148931754739085751566117)
                  ·
                    rfl

theorem cell21_652598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_652598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652598 prefixEnd_652598 := by exact prefixLift 652598
  have htrace : WordTrace (prefixWord ++ tailWord_652598) baseStart_652598 baseEnd_652598 := by
    simpa [prefixWord, tailWord_652598, baseEnd_652598] using wordTrace_append hprefix tailTrace_652598
  have hstable : (prefixWord ++ tailWord_652598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652598).length < 2 ^ (prefixWord ++ tailWord_652598).sum := by decide
  have hdescent : baseEnd_652598 < baseStart_652598 := by decide
  rcases family_descends (prefixWord ++ tailWord_652598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652606 : List Nat := [4, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_652606 : Nat := 118140960795 + 652606 * 2 ^ 59
def prefixEnd_652606 : Nat := 4983230072969 + 3 ^ 40 * 652606 * 2
def baseEnd_652606 : Nat := 148933580448079515432767

theorem tailTrace_652606 : CollatzResearch.WordTrace tailWord_652606 prefixEnd_652606 148933580448079515432767 := by
  unfold tailWord_652606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2975312034215924134553209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15868330849151595384283781 2975312034215924134553209)
  ·
    refine ⟨2231484025661943100914907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2975312034215924134553209 2231484025661943100914907)
    ·
      refine ⟨3347226038492914651372361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2231484025661943100914907 3347226038492914651372361)
      ·
        refine ⟨2510419528869685988529271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3347226038492914651372361 2510419528869685988529271)
        ·
          refine ⟨3765629293304528982793907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2510419528869685988529271 3765629293304528982793907)
          ·
            refine ⟨5648443939956793474190861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765629293304528982793907 5648443939956793474190861)
            ·
              refine ⟨2118166477483797552821573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5648443939956793474190861 2118166477483797552821573)
              ·
                refine ⟨397156214528212041154045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2118166477483797552821573 397156214528212041154045)
                ·
                  refine ⟨148933580448079515432767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397156214528212041154045 148933580448079515432767)
                  ·
                    rfl

theorem cell21_652606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_652606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652606 prefixEnd_652606 := by exact prefixLift 652606
  have htrace : WordTrace (prefixWord ++ tailWord_652606) baseStart_652606 baseEnd_652606 := by
    simpa [prefixWord, tailWord_652606, baseEnd_652606] using wordTrace_append hprefix tailTrace_652606
  have hstable : (prefixWord ++ tailWord_652606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652606).length < 2 ^ (prefixWord ++ tailWord_652606).sum := by decide
  have hdescent : baseEnd_652606 < baseStart_652606 := by decide
  rcases family_descends (prefixWord ++ tailWord_652606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652617 : List Nat := [1, 2, 1, 1, 2, 3, 5, 6]
def baseStart_652617 : Nat := 118140960795 + 652617 * 2 ^ 59
def prefixEnd_652617 : Nat := 4983230072969 + 3 ^ 40 * 652617 * 2
def baseEnd_652617 : Nat := 49645363599315313583137

theorem tailTrace_652617 : CollatzResearch.WordTrace tailWord_652617 prefixEnd_652617 49645363599315313583137 := by
  unfold tailWord_652617
  simp only [CollatzResearch.WordTrace]
  refine ⟨23802897476687541955076105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15868598317791694636717403 23802897476687541955076105)
  ·
    refine ⟨17852173107515656466307079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23802897476687541955076105 17852173107515656466307079)
    ·
      refine ⟨26778259661273484699460619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17852173107515656466307079 26778259661273484699460619)
      ·
        refine ⟨40167389491910227049190929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26778259661273484699460619 40167389491910227049190929)
        ·
          refine ⟨30125542118932670286893197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40167389491910227049190929 30125542118932670286893197)
          ·
            refine ⟨11297078294599751357584949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30125542118932670286893197 11297078294599751357584949)
            ·
              refine ⟨1059101090118726689773589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11297078294599751357584949 1059101090118726689773589)
              ·
                refine ⟨49645363599315313583137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1059101090118726689773589 49645363599315313583137)
                ·
                  rfl

theorem cell21_652617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 6].length) (baseStart_652617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652617 prefixEnd_652617 := by exact prefixLift 652617
  have htrace : WordTrace (prefixWord ++ tailWord_652617) baseStart_652617 baseEnd_652617 := by
    simpa [prefixWord, tailWord_652617, baseEnd_652617] using wordTrace_append hprefix tailTrace_652617
  have hstable : (prefixWord ++ tailWord_652617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652617).length < 2 ^ (prefixWord ++ tailWord_652617).sum := by decide
  have hdescent : baseEnd_652617 < baseStart_652617 := by decide
  rcases family_descends (prefixWord ++ tailWord_652617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652654 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_652654 : Nat := 118140960795 + 652654 * 2 ^ 59
def prefixEnd_652654 : Nat := 4983230072969 + 3 ^ 40 * 652654 * 2
def baseEnd_652654 : Nat := 148944534702042098632669

theorem tailTrace_652654 : CollatzResearch.WordTrace tailWord_652654 prefixEnd_652654 148944534702042098632669 := by
  unfold tailWord_652654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2975530872194187159271627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15869497985035664849448677 2975530872194187159271627)
  ·
    refine ⟨4463296308291280738907441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2975530872194187159271627 4463296308291280738907441)
    ·
      refine ⟨3347472231218460554180581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4463296308291280738907441 3347472231218460554180581)
      ·
        refine ⟨627651043353461353908859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3347472231218460554180581 627651043353461353908859)
        ·
          refine ⟨941476565030192030863289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627651043353461353908859 941476565030192030863289)
          ·
            refine ⟨706107423772644023147467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 941476565030192030863289 706107423772644023147467)
            ·
              refine ⟨1059161135658966034721201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706107423772644023147467 1059161135658966034721201)
              ·
                refine ⟨794370851744224526040901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1059161135658966034721201 794370851744224526040901)
                ·
                  refine ⟨148944534702042098632669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 794370851744224526040901 148944534702042098632669)
                  ·
                    rfl

theorem cell21_652654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_652654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652654 prefixEnd_652654 := by exact prefixLift 652654
  have htrace : WordTrace (prefixWord ++ tailWord_652654) baseStart_652654 baseEnd_652654 := by
    simpa [prefixWord, tailWord_652654, baseEnd_652654] using wordTrace_append hprefix tailTrace_652654
  have hstable : (prefixWord ++ tailWord_652654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652654).length < 2 ^ (prefixWord ++ tailWord_652654).sum := by decide
  have hdescent : baseEnd_652654 < baseStart_652654 := by decide
  rcases family_descends (prefixWord ++ tailWord_652654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652665 : List Nat := [1, 2, 1, 3, 2, 1, 4, 4, 3]
def baseStart_652665 : Nat := 118140960795 + 652665 * 2 ^ 59
def prefixEnd_652665 : Nat := 4983230072969 + 3 ^ 40 * 652665 * 2
def baseEnd_652665 : Nat := 148947045051908523949313

theorem tailTrace_652665 : CollatzResearch.WordTrace tailWord_652665 prefixEnd_652665 148947045051908523949313 := by
  unfold tailWord_652665
  simp only [CollatzResearch.WordTrace]
  refine ⟨23804648180513646152823449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15869765453675764101882299 23804648180513646152823449)
  ·
    refine ⟨17853486135385234614617587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23804648180513646152823449 17853486135385234614617587)
    ·
      refine ⟨26780229203077851921926381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17853486135385234614617587 26780229203077851921926381)
      ·
        refine ⟨10042585951154194470722393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26780229203077851921926381 10042585951154194470722393)
        ·
          refine ⟨7531939463365645853041795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10042585951154194470722393 7531939463365645853041795)
          ·
            refine ⟨11297909195048468779562693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7531939463365645853041795 11297909195048468779562693)
            ·
              refine ⟨2118357974071587896168005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11297909195048468779562693 2118357974071587896168005)
              ·
                refine ⟨397192120138422730531501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2118357974071587896168005 397192120138422730531501)
                ·
                  refine ⟨148947045051908523949313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397192120138422730531501 148947045051908523949313)
                  ·
                    rfl

theorem cell21_652665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 3].length) (baseStart_652665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652665 prefixEnd_652665 := by exact prefixLift 652665
  have htrace : WordTrace (prefixWord ++ tailWord_652665) baseStart_652665 baseEnd_652665 := by
    simpa [prefixWord, tailWord_652665, baseEnd_652665] using wordTrace_append hprefix tailTrace_652665
  have hstable : (prefixWord ++ tailWord_652665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652665).length < 2 ^ (prefixWord ++ tailWord_652665).sum := by decide
  have hdescent : baseEnd_652665 < baseStart_652665 := by decide
  rcases family_descends (prefixWord ++ tailWord_652665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_652775 : List Nat := [1, 1, 5, 2, 1, 4, 2, 2, 3]
def baseStart_652775 : Nat := 118140960795 + 652775 * 2 ^ 59
def prefixEnd_652775 : Nat := 4983230072969 + 3 ^ 40 * 652775 * 2
def baseEnd_652775 : Nat := 148972148550572777115755

theorem tailTrace_652775 : CollatzResearch.WordTrace tailWord_652775 prefixEnd_652775 148972148550572777115755 := by
  unfold tailWord_652775
  simp only [CollatzResearch.WordTrace]
  refine ⟨23808660210115134939327779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15872440140076756626218519 23808660210115134939327779)
  ·
    refine ⟨35712990315172702408991669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23808660210115134939327779 35712990315172702408991669)
    ·
      refine ⟨3348092842047440850842969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35712990315172702408991669 3348092842047440850842969)
      ·
        refine ⟨2511069631535580638132227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3348092842047440850842969 2511069631535580638132227)
        ·
          refine ⟨3766604447303370957198341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511069631535580638132227 3766604447303370957198341)
          ·
            refine ⟨706238333869382054474689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3766604447303370957198341 706238333869382054474689)
            ·
              refine ⟨529678750402036540856017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706238333869382054474689 529678750402036540856017)
              ·
                refine ⟨397259062801527405642013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529678750402036540856017 397259062801527405642013)
                ·
                  refine ⟨148972148550572777115755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397259062801527405642013 148972148550572777115755)
                  ·
                    rfl

theorem cell21_652775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 3].length) (baseStart_652775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_652775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_652775 prefixEnd_652775 := by exact prefixLift 652775
  have htrace : WordTrace (prefixWord ++ tailWord_652775) baseStart_652775 baseEnd_652775 := by
    simpa [prefixWord, tailWord_652775, baseEnd_652775] using wordTrace_append hprefix tailTrace_652775
  have hstable : (prefixWord ++ tailWord_652775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_652775).length < 2 ^ (prefixWord ++ tailWord_652775).sum := by decide
  have hdescent : baseEnd_652775 < baseStart_652775 := by decide
  rcases family_descends (prefixWord ++ tailWord_652775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
