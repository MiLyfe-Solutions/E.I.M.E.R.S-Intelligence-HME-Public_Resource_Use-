import V185TrunkScan23Chunk0690

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4086590 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_4086590 : Nat := 118140960795 + 4086590 * 2 ^ 59
def prefixEnd_4086590 : Nat := 4983230072969 + 3 ^ 40 * 4086590 * 2
def baseEnd_4086590 : Nat := 2098384907857271431531121

theorem tailTrace_4086590 : CollatzResearch.WordTrace tailWord_4086590 prefixEnd_4086590 2098384907857271431531121 := by
  unfold tailWord_4086590
  simp only [CollatzResearch.WordTrace]
  refine ⟨18631272783123729856468153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99366788176659892567830149 18631272783123729856468153)
  ·
    refine ⟨13973454587342797392351115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18631272783123729856468153 13973454587342797392351115)
    ·
      refine ⟨20960181881014196088526673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13973454587342797392351115 20960181881014196088526673)
      ·
        refine ⟨15720136410760647066395005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20960181881014196088526673 15720136410760647066395005)
        ·
          refine ⟨5895051154035242649898127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15720136410760647066395005 5895051154035242649898127)
          ·
            refine ⟨8842576731052863974847191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5895051154035242649898127 8842576731052863974847191)
            ·
              refine ⟨13263865096579295962270787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8842576731052863974847191 13263865096579295962270787)
              ·
                refine ⟨19895797644868943943406181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13263865096579295962270787 19895797644868943943406181)
                ·
                  refine ⟨3730462058412926989388659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19895797644868943943406181 3730462058412926989388659)
                  ·
                    refine ⟨5595693087619390484082989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3730462058412926989388659 5595693087619390484082989)
                    ·
                      refine ⟨2098384907857271431531121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5595693087619390484082989 2098384907857271431531121)
                      ·
                        rfl

theorem cell23_4086590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_4086590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086590 prefixEnd_4086590 := by exact prefixLift 4086590
  have htrace : WordTrace (prefixWord ++ tailWord_4086590) baseStart_4086590 baseEnd_4086590 := by
    simpa [prefixWord, tailWord_4086590, baseEnd_4086590] using wordTrace_append hprefix tailTrace_4086590
  have hstable : (prefixWord ++ tailWord_4086590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086590).length < 2 ^ (prefixWord ++ tailWord_4086590).sum := by decide
  have hdescent : baseEnd_4086590 < baseStart_4086590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086599 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_4086599 : Nat := 118140960795 + 4086599 * 2 ^ 59
def prefixEnd_4086599 : Nat := 4983230072969 + 3 ^ 40 * 4086599 * 2
def baseEnd_4086599 : Nat := 2098389529183161896318579

theorem tailTrace_4086599 : CollatzResearch.WordTrace tailWord_4086599 prefixEnd_4086599 2098389529183161896318579 := by
  unfold tailWord_4086599
  simp only [CollatzResearch.WordTrace]
  refine ⟨149050510521957233388822851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99367007014638155592548567 149050510521957233388822851)
  ·
    refine ⟨223575765782935850083234277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149050510521957233388822851 223575765782935850083234277)
    ·
      refine ⟨41920456084300471890606427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223575765782935850083234277 41920456084300471890606427)
      ·
        refine ⟨62880684126450707835909641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41920456084300471890606427 62880684126450707835909641)
        ·
          refine ⟨47160513094838030876932231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62880684126450707835909641 47160513094838030876932231)
          ·
            refine ⟨70740769642257046315398347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47160513094838030876932231 70740769642257046315398347)
            ·
              refine ⟨106111154463385569473097521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70740769642257046315398347 106111154463385569473097521)
              ·
                refine ⟨79583365847539177104823141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106111154463385569473097521 79583365847539177104823141)
                ·
                  refine ⟨14921881096413595707154339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79583365847539177104823141 14921881096413595707154339)
                  ·
                    refine ⟨22382821644620393560731509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14921881096413595707154339 22382821644620393560731509)
                    ·
                      refine ⟨2098389529183161896318579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22382821644620393560731509 2098389529183161896318579)
                      ·
                        rfl

theorem cell23_4086599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_4086599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086599 prefixEnd_4086599 := by exact prefixLift 4086599
  have htrace : WordTrace (prefixWord ++ tailWord_4086599) baseStart_4086599 baseEnd_4086599 := by
    simpa [prefixWord, tailWord_4086599, baseEnd_4086599] using wordTrace_append hprefix tailTrace_4086599
  have hstable : (prefixWord ++ tailWord_4086599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086599).length < 2 ^ (prefixWord ++ tailWord_4086599).sum := by decide
  have hdescent : baseEnd_4086599 < baseStart_4086599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086658 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_4086658 : Nat := 118140960795 + 4086658 * 2 ^ 59
def prefixEnd_4086658 : Nat := 4983230072969 + 3 ^ 40 * 4086658 * 2
def baseEnd_4086658 : Nat := 2098419824541777165480809

theorem tailTrace_4086658 : CollatzResearch.WordTrace tailWord_4086658 prefixEnd_4086658 2098419824541777165480809 := by
  unfold tailWord_4086658
  simp only [CollatzResearch.WordTrace]
  refine ⟨37263165607185871616305157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99368441619162324310147085 37263165607185871616305157)
  ·
    refine ⟨6986843551347350928057217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37263165607185871616305157 6986843551347350928057217)
    ·
      refine ⟨5240132663510513196042913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6986843551347350928057217 5240132663510513196042913)
      ·
        refine ⟨3930099497632884897032185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5240132663510513196042913 3930099497632884897032185)
        ·
          refine ⟨2947574623224663672774139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3930099497632884897032185 2947574623224663672774139)
          ·
            refine ⟨4421361934836995509161209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947574623224663672774139 4421361934836995509161209)
            ·
              refine ⟨3316021451127746631870907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4421361934836995509161209 3316021451127746631870907)
              ·
                refine ⟨4974032176691619947806361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316021451127746631870907 4974032176691619947806361)
                ·
                  refine ⟨3730524132518714960854771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4974032176691619947806361 3730524132518714960854771)
                  ·
                    refine ⟨5595786198778072441282157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3730524132518714960854771 5595786198778072441282157)
                    ·
                      refine ⟨2098419824541777165480809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5595786198778072441282157 2098419824541777165480809)
                      ·
                        rfl

theorem cell23_4086658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_4086658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086658 prefixEnd_4086658 := by exact prefixLift 4086658
  have htrace : WordTrace (prefixWord ++ tailWord_4086658) baseStart_4086658 baseEnd_4086658 := by
    simpa [prefixWord, tailWord_4086658, baseEnd_4086658] using wordTrace_append hprefix tailTrace_4086658
  have hstable : (prefixWord ++ tailWord_4086658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086658).length < 2 ^ (prefixWord ++ tailWord_4086658).sum := by decide
  have hdescent : baseEnd_4086658 < baseStart_4086658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086664 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 2, 2, 2]
def baseStart_4086664 : Nat := 118140960795 + 4086664 * 2 ^ 59
def prefixEnd_4086664 : Nat := 4983230072969 + 3 ^ 40 * 4086664 * 2
def baseEnd_4086664 : Nat := 2098422905425704142005781

theorem tailTrace_4086664 : CollatzResearch.WordTrace tailWord_4086664 prefixEnd_4086664 2098422905425704142005781 := by
  unfold tailWord_4086664
  simp only [CollatzResearch.WordTrace]
  refine ⟨74526440633360874744969523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99368587511147832993292697 74526440633360874744969523)
  ·
    refine ⟨111789660950041312117454285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74526440633360874744969523 111789660950041312117454285)
    ·
      refine ⟨41921122856265492044045357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111789660950041312117454285 41921122856265492044045357)
      ·
        refine ⟨15720421071099559516517009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41921122856265492044045357 15720421071099559516517009)
        ·
          refine ⟨11790315803324669637387757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15720421071099559516517009 11790315803324669637387757)
          ·
            refine ⟨4421368426246751114020409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11790315803324669637387757 4421368426246751114020409)
            ·
              refine ⟨3316026319685063335515307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4421368426246751114020409 3316026319685063335515307)
              ·
                refine ⟨4974039479527595003272961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316026319685063335515307 4974039479527595003272961)
                ·
                  refine ⟨3730529609645696252454721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4974039479527595003272961 3730529609645696252454721)
                  ·
                    refine ⟨2797897207234272189341041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3730529609645696252454721 2797897207234272189341041)
                    ·
                      refine ⟨2098422905425704142005781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797897207234272189341041 2098422905425704142005781)
                      ·
                        rfl

theorem cell23_4086664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_4086664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086664 prefixEnd_4086664 := by exact prefixLift 4086664
  have htrace : WordTrace (prefixWord ++ tailWord_4086664) baseStart_4086664 baseEnd_4086664 := by
    simpa [prefixWord, tailWord_4086664, baseEnd_4086664] using wordTrace_append hprefix tailTrace_4086664
  have hstable : (prefixWord ++ tailWord_4086664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086664).length < 2 ^ (prefixWord ++ tailWord_4086664).sum := by decide
  have hdescent : baseEnd_4086664 < baseStart_4086664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086676 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_4086676 : Nat := 118140960795 + 4086676 * 2 ^ 59
def prefixEnd_4086676 : Nat := 4983230072969 + 3 ^ 40 * 4086676 * 2
def baseEnd_4086676 : Nat := 2098429067193558095055725

theorem tailTrace_4086676 : CollatzResearch.WordTrace tailWord_4086676 prefixEnd_4086676 2098429067193558095055725 := by
  unfold tailWord_4086676
  simp only [CollatzResearch.WordTrace]
  refine ⟨74526659471339137769687941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99368879295118850359583921 74526659471339137769687941)
  ·
    refine ⟨13973748650876088331816489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74526659471339137769687941 13973748650876088331816489)
    ·
      refine ⟨10480311488157066248862367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13973748650876088331816489 10480311488157066248862367)
      ·
        refine ⟨15720467232235599373293551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10480311488157066248862367 15720467232235599373293551)
        ·
          refine ⟨23580700848353399059940327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15720467232235599373293551 23580700848353399059940327)
          ·
            refine ⟨35371051272530098589910491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23580700848353399059940327 35371051272530098589910491)
            ·
              refine ⟨53056576908795147884865737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35371051272530098589910491 53056576908795147884865737)
              ·
                refine ⟨39792432681596360913649303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53056576908795147884865737 39792432681596360913649303)
                ·
                  refine ⟨59688649022394541370473955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39792432681596360913649303 59688649022394541370473955)
                  ·
                    refine ⟨89532973533591812055710933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59688649022394541370473955 89532973533591812055710933)
                    ·
                      refine ⟨2098429067193558095055725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89532973533591812055710933 2098429067193558095055725)
                      ·
                        rfl

theorem cell23_4086676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_4086676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086676 prefixEnd_4086676 := by exact prefixLift 4086676
  have htrace : WordTrace (prefixWord ++ tailWord_4086676) baseStart_4086676 baseEnd_4086676 := by
    simpa [prefixWord, tailWord_4086676, baseEnd_4086676] using wordTrace_append hprefix tailTrace_4086676
  have hstable : (prefixWord ++ tailWord_4086676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086676).length < 2 ^ (prefixWord ++ tailWord_4086676).sum := by decide
  have hdescent : baseEnd_4086676 < baseStart_4086676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086699 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 6]
def baseStart_4086699 : Nat := 118140960795 + 4086699 * 2 ^ 59
def prefixEnd_4086699 : Nat := 4983230072969 + 3 ^ 40 * 4086699 * 2
def baseEnd_4086699 : Nat := 2098440877248611505068119

theorem tailTrace_4086699 : CollatzResearch.WordTrace tailWord_4086699 prefixEnd_4086699 2098440877248611505068119 := by
  unfold tailWord_4086699
  simp only [CollatzResearch.WordTrace]
  refine ⟨149054157821594950467463151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99369438547729966978308767 149054157821594950467463151)
  ·
    refine ⟨223581236732392425701194727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149054157821594950467463151 223581236732392425701194727)
    ·
      refine ⟨335371855098588638551792091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223581236732392425701194727 335371855098588638551792091)
      ·
        refine ⟨503057782647882957827688137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335371855098588638551792091 503057782647882957827688137)
        ·
          refine ⟨377293336985912218370766103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503057782647882957827688137 377293336985912218370766103)
          ·
            refine ⟨565940005478868327556149155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377293336985912218370766103 565940005478868327556149155)
            ·
              refine ⟨848910008218302491334223733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565940005478868327556149155 848910008218302491334223733)
              ·
                refine ⟨79585313270465858562583475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 848910008218302491334223733 79585313270465858562583475)
                ·
                  refine ⟨119377969905698787843875213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79585313270465858562583475 119377969905698787843875213)
                  ·
                    refine ⟨44766738714637045441453205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119377969905698787843875213 44766738714637045441453205)
                    ·
                      refine ⟨2098440877248611505068119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44766738714637045441453205 2098440877248611505068119)
                      ·
                        rfl

theorem cell23_4086699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_4086699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086699 prefixEnd_4086699 := by exact prefixLift 4086699
  have htrace : WordTrace (prefixWord ++ tailWord_4086699) baseStart_4086699 baseEnd_4086699 := by
    simpa [prefixWord, tailWord_4086699, baseEnd_4086699] using wordTrace_append hprefix tailTrace_4086699
  have hstable : (prefixWord ++ tailWord_4086699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086699).length < 2 ^ (prefixWord ++ tailWord_4086699).sum := by decide
  have hdescent : baseEnd_4086699 < baseStart_4086699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086706 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_4086706 : Nat := 118140960795 + 4086706 * 2 ^ 59
def prefixEnd_4086706 : Nat := 4983230072969 + 3 ^ 40 * 4086706 * 2
def baseEnd_4086706 : Nat := 2098444471613192977680587

theorem tailTrace_4086706 : CollatzResearch.WordTrace tailWord_4086706 prefixEnd_4086706 2098444471613192977680587 := by
  unfold tailWord_4086706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37263603283142397665741993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99369608755046393775311981 37263603283142397665741993)
  ·
    refine ⟨27947702462356798249306495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37263603283142397665741993 27947702462356798249306495)
    ·
      refine ⟨41921553693535197373959743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27947702462356798249306495 41921553693535197373959743)
      ·
        refine ⟨62882330540302796060939615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41921553693535197373959743 62882330540302796060939615)
        ·
          refine ⟨94323495810454194091409423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62882330540302796060939615 94323495810454194091409423)
          ·
            refine ⟨141485243715681291137114135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94323495810454194091409423 141485243715681291137114135)
            ·
              refine ⟨212227865573521936705671203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141485243715681291137114135 212227865573521936705671203)
              ·
                refine ⟨318341798360282905058506805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212227865573521936705671203 318341798360282905058506805)
                ·
                  refine ⟨29844543596276522349235013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318341798360282905058506805 29844543596276522349235013)
                  ·
                    refine ⟨5595851924301847940481565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29844543596276522349235013 5595851924301847940481565)
                    ·
                      refine ⟨2098444471613192977680587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5595851924301847940481565 2098444471613192977680587)
                      ·
                        rfl

theorem cell23_4086706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_4086706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086706 prefixEnd_4086706 := by exact prefixLift 4086706
  have htrace : WordTrace (prefixWord ++ tailWord_4086706) baseStart_4086706 baseEnd_4086706 := by
    simpa [prefixWord, tailWord_4086706, baseEnd_4086706] using wordTrace_append hprefix tailTrace_4086706
  have hstable : (prefixWord ++ tailWord_4086706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086706).length < 2 ^ (prefixWord ++ tailWord_4086706).sum := by decide
  have hdescent : baseEnd_4086706 < baseStart_4086706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086740 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_4086740 : Nat := 118140960795 + 4086740 * 2 ^ 59
def prefixEnd_4086740 : Nat := 4983230072969 + 3 ^ 40 * 4086740 * 2
def baseEnd_4086740 : Nat := 2098461929955445844655431

theorem tailTrace_4086740 : CollatzResearch.WordTrace tailWord_4086740 prefixEnd_4086740 2098461929955445844655431 := by
  unfold tailWord_4086740
  simp only [CollatzResearch.WordTrace]
  refine ⟨74527826607223207234852837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99370435476297609646470449 74527826607223207234852837)
  ·
    refine ⟨13973967488854351356534907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74527826607223207234852837 13973967488854351356534907)
    ·
      refine ⟨20960951233281527034802361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13973967488854351356534907 20960951233281527034802361)
      ·
        refine ⟨15720713424961145276101771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20960951233281527034802361 15720713424961145276101771)
        ·
          refine ⟨23581070137441717914152657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15720713424961145276101771 23581070137441717914152657)
          ·
            refine ⟨17685802603081288435614493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23581070137441717914152657 17685802603081288435614493)
            ·
              refine ⟨6632175976155483163355435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17685802603081288435614493 6632175976155483163355435)
              ·
                refine ⟨9948263964233224745033153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632175976155483163355435 9948263964233224745033153)
                ·
                  refine ⟨7461197973174918558774865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9948263964233224745033153 7461197973174918558774865)
                  ·
                    refine ⟨5595898479881188919081149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7461197973174918558774865 5595898479881188919081149)
                    ·
                      refine ⟨2098461929955445844655431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5595898479881188919081149 2098461929955445844655431)
                      ·
                        rfl

theorem cell23_4086740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_4086740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086740 prefixEnd_4086740 := by exact prefixLift 4086740
  have htrace : WordTrace (prefixWord ++ tailWord_4086740) baseStart_4086740 baseEnd_4086740 := by
    simpa [prefixWord, tailWord_4086740, baseEnd_4086740] using wordTrace_append hprefix tailTrace_4086740
  have hstable : (prefixWord ++ tailWord_4086740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086740).length < 2 ^ (prefixWord ++ tailWord_4086740).sum := by decide
  have hdescent : baseEnd_4086740 < baseStart_4086740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086753 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_4086753 : Nat := 118140960795 + 4086753 * 2 ^ 59
def prefixEnd_4086753 : Nat := 4983230072969 + 3 ^ 40 * 4086753 * 2
def baseEnd_4086753 : Nat := 2098468605203954293792871

theorem tailTrace_4086753 : CollatzResearch.WordTrace tailWord_4086753 prefixEnd_4086753 2098468605203954293792871 := by
  unfold tailWord_4086753
  simp only [CollatzResearch.WordTrace]
  refine ⟨149056127363399317689928913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99370751575599545126619275 149056127363399317689928913)
  ·
    refine ⟨111792095522549488267446685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149056127363399317689928913 111792095522549488267446685)
    ·
      refine ⟨41922035820956058100292507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111792095522549488267446685 41922035820956058100292507)
      ·
        refine ⟨62883053731434087150438761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41922035820956058100292507 62883053731434087150438761)
        ·
          refine ⟨47162290298575565362829071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62883053731434087150438761 47162290298575565362829071)
          ·
            refine ⟨70743435447863348044243607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47162290298575565362829071 70743435447863348044243607)
            ·
              refine ⟨106115153171795022066365411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70743435447863348044243607 106115153171795022066365411)
              ·
                refine ⟨159172729757692533099548117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106115153171795022066365411 159172729757692533099548117)
                ·
                  refine ⟨3730610853695918744520659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 159172729757692533099548117 3730610853695918744520659)
                  ·
                    refine ⟨5595916280543878116780989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3730610853695918744520659 5595916280543878116780989)
                    ·
                      refine ⟨2098468605203954293792871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5595916280543878116780989 2098468605203954293792871)
                      ·
                        rfl

theorem cell23_4086753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_4086753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086753 prefixEnd_4086753 := by exact prefixLift 4086753
  have htrace : WordTrace (prefixWord ++ tailWord_4086753) baseStart_4086753 baseEnd_4086753 := by
    simpa [prefixWord, tailWord_4086753, baseEnd_4086753] using wordTrace_append hprefix tailTrace_4086753
  have hstable : (prefixWord ++ tailWord_4086753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086753).length < 2 ^ (prefixWord ++ tailWord_4086753).sum := by decide
  have hdescent : baseEnd_4086753 < baseStart_4086753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086756 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_4086756 : Nat := 118140960795 + 4086756 * 2 ^ 59
def prefixEnd_4086756 : Nat := 4983230072969 + 3 ^ 40 * 4086756 * 2
def baseEnd_4086756 : Nat := 699490048548639260685119

theorem tailTrace_4086756 : CollatzResearch.WordTrace tailWord_4086756 prefixEnd_4086756 699490048548639260685119 := by
  unfold tailWord_4086756
  simp only [CollatzResearch.WordTrace]
  refine ⟨74528118391194224601144061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99370824521592299468192081 74528118391194224601144061)
  ·
    refine ⟨27948044396697834225429023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74528118391194224601144061 27948044396697834225429023)
    ·
      refine ⟨41922066595046751338143535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27948044396697834225429023 41922066595046751338143535)
      ·
        refine ⟨62883099892570127007215303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41922066595046751338143535 62883099892570127007215303)
        ·
          refine ⟨94324649838855190510822955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62883099892570127007215303 94324649838855190510822955)
          ·
            refine ⟨141486974758282785766234433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94324649838855190510822955 141486974758282785766234433)
            ·
              refine ⟨106115231068712089324675825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141486974758282785766234433 106115231068712089324675825)
              ·
                refine ⟨79586423301534066993506869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106115231068712089324675825 79586423301534066993506869)
                ·
                  refine ⟨7461227184518818780641269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79586423301534066993506869 7461227184518818780641269)
                  ·
                    refine ⟨699490048548639260685119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7461227184518818780641269 699490048548639260685119)
                    ·
                      rfl

theorem cell23_4086756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_4086756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086756 prefixEnd_4086756 := by exact prefixLift 4086756
  have htrace : WordTrace (prefixWord ++ tailWord_4086756) baseStart_4086756 baseEnd_4086756 := by
    simpa [prefixWord, tailWord_4086756, baseEnd_4086756] using wordTrace_append hprefix tailTrace_4086756
  have hstable : (prefixWord ++ tailWord_4086756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086756).length < 2 ^ (prefixWord ++ tailWord_4086756).sum := by decide
  have hdescent : baseEnd_4086756 < baseStart_4086756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086820 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_4086820 : Nat := 118140960795 + 4086820 * 2 ^ 59
def prefixEnd_4086820 : Nat := 4983230072969 + 3 ^ 40 * 4086820 * 2
def baseEnd_4086820 : Nat := 699501002802601843885021

theorem tailTrace_4086820 : CollatzResearch.WordTrace tailWord_4086820 prefixEnd_4086820 699501002802601843885021 := by
  unfold tailWord_4086820
  simp only [CollatzResearch.WordTrace]
  refine ⟨74529285527078294066308957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99372380702771058755078609 74529285527078294066308957)
  ·
    refine ⟨27948482072654360274865859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74529285527078294066308957 27948482072654360274865859)
    ·
      refine ⟨41922723108981540412298789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27948482072654360274865859 41922723108981540412298789)
      ·
        refine ⟨7860510582934038827306023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41922723108981540412298789 7860510582934038827306023)
        ·
          refine ⟨11790765874401058240959035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7860510582934038827306023 11790765874401058240959035)
          ·
            refine ⟨17686148811601587361438553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11790765874401058240959035 17686148811601587361438553)
            ·
              refine ⟨13264611608701190521078915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17686148811601587361438553 13264611608701190521078915)
              ·
                refine ⟨19896917413051785781618373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264611608701190521078915 19896917413051785781618373)
                ·
                  refine ⟨3730672014947209834053445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19896917413051785781618373 3730672014947209834053445)
                  ·
                    refine ⟨699501002802601843885021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3730672014947209834053445 699501002802601843885021)
                    ·
                      rfl

theorem cell23_4086820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_4086820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086820 prefixEnd_4086820 := by exact prefixLift 4086820
  have htrace : WordTrace (prefixWord ++ tailWord_4086820) baseStart_4086820 baseEnd_4086820 := by
    simpa [prefixWord, tailWord_4086820, baseEnd_4086820] using wordTrace_append hprefix tailTrace_4086820
  have hstable : (prefixWord ++ tailWord_4086820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086820).length < 2 ^ (prefixWord ++ tailWord_4086820).sum := by decide
  have hdescent : baseEnd_4086820 < baseStart_4086820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086830 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_4086830 : Nat := 118140960795 + 4086830 * 2 ^ 59
def prefixEnd_4086830 : Nat := 4983230072969 + 3 ^ 40 * 4086830 * 2
def baseEnd_4086830 : Nat := 2098508143214350492530017

theorem tailTrace_4086830 : CollatzResearch.WordTrace tailWord_4086830 prefixEnd_4086830 2098508143214350492530017 := by
  unfold tailWord_4086830
  simp only [CollatzResearch.WordTrace]
  refine ⟨18632366973015044980060243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99372623856080239893654629 18632366973015044980060243)
  ·
    refine ⟨27948550459522567470090365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18632366973015044980060243 27948550459522567470090365)
    ·
      refine ⟨10480706422320962801283887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27948550459522567470090365 10480706422320962801283887)
      ·
        refine ⟨15721059633481444201925831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10480706422320962801283887 15721059633481444201925831)
        ·
          refine ⟨23581589450222166302888747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15721059633481444201925831 23581589450222166302888747)
          ·
            refine ⟨35372384175333249454333121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23581589450222166302888747 35372384175333249454333121)
            ·
              refine ⟨26529288131499937090749841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35372384175333249454333121 26529288131499937090749841)
              ·
                refine ⟨19896966098624952818062381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26529288131499937090749841 19896966098624952818062381)
                ·
                  refine ⟨7461362286984357306773393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19896966098624952818062381 7461362286984357306773393)
                  ·
                    refine ⟨5596021715238267980080045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7461362286984357306773393 5596021715238267980080045)
                    ·
                      refine ⟨2098508143214350492530017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5596021715238267980080045 2098508143214350492530017)
                      ·
                        rfl

theorem cell23_4086830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_4086830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086830 prefixEnd_4086830 := by exact prefixLift 4086830
  have htrace : WordTrace (prefixWord ++ tailWord_4086830) baseStart_4086830 baseEnd_4086830 := by
    simpa [prefixWord, tailWord_4086830, baseEnd_4086830] using wordTrace_append hprefix tailTrace_4086830
  have hstable : (prefixWord ++ tailWord_4086830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086830).length < 2 ^ (prefixWord ++ tailWord_4086830).sum := by decide
  have hdescent : baseEnd_4086830 < baseStart_4086830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086893 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_4086893 : Nat := 118140960795 + 4086893 * 2 ^ 59
def prefixEnd_4086893 : Nat := 4983230072969 + 3 ^ 40 * 4086893 * 2
def baseEnd_4086893 : Nat := 699513497498527915347409

theorem tailTrace_4086893 : CollatzResearch.WordTrace tailWord_4086893 prefixEnd_4086893 699513497498527915347409 := by
  unfold tailWord_4086893
  simp only [CollatzResearch.WordTrace]
  refine ⟨149061233582892121600025333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99374155721928081066683555 149061233582892121600025333)
  ·
    refine ⟨13974490648396136400002375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149061233582892121600025333 13974490648396136400002375)
    ·
      refine ⟨20961735972594204600003563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13974490648396136400002375 20961735972594204600003563)
      ·
        refine ⟨31442603958891306900005345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20961735972594204600003563 31442603958891306900005345)
        ·
          refine ⟨23581952969168480175004009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31442603958891306900005345 23581952969168480175004009)
          ·
            refine ⟨17686464726876360131253007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23581952969168480175004009 17686464726876360131253007)
            ·
              refine ⟨26529697090314540196879511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17686464726876360131253007 26529697090314540196879511)
              ·
                refine ⟨39794545635471810295319267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26529697090314540196879511 39794545635471810295319267)
                ·
                  refine ⟨59691818453207715442978901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39794545635471810295319267 59691818453207715442978901)
                  ·
                    refine ⟨699513497498527915347409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59691818453207715442978901 699513497498527915347409)
                    ·
                      rfl

theorem cell23_4086893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_4086893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086893 prefixEnd_4086893 := by exact prefixLift 4086893
  have htrace : WordTrace (prefixWord ++ tailWord_4086893) baseStart_4086893 baseEnd_4086893 := by
    simpa [prefixWord, tailWord_4086893, baseEnd_4086893] using wordTrace_append hprefix tailTrace_4086893
  have hstable : (prefixWord ++ tailWord_4086893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086893).length < 2 ^ (prefixWord ++ tailWord_4086893).sum := by decide
  have hdescent : baseEnd_4086893 < baseStart_4086893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086903 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 3]
def baseStart_4086903 : Nat := 118140960795 + 4086903 * 2 ^ 59
def prefixEnd_4086903 : Nat := 4983230072969 + 3 ^ 40 * 4086903 * 2
def baseEnd_4086903 : Nat := 2098545627302128706917181

theorem tailTrace_4086903 : CollatzResearch.WordTrace tailWord_4086903 prefixEnd_4086903 2098545627302128706917181 := by
  unfold tailWord_4086903
  simp only [CollatzResearch.WordTrace]
  refine ⟨149061598312855893307889363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99374398875237262205259575 149061598312855893307889363)
  ·
    refine ⟨223592397469283839961834045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149061598312855893307889363 223592397469283839961834045)
    ·
      refine ⟨83847149050981439985687767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223592397469283839961834045 83847149050981439985687767)
      ·
        refine ⟨125770723576472159978531651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83847149050981439985687767 125770723576472159978531651)
        ·
          refine ⟨188656085364708239967797477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125770723576472159978531651 188656085364708239967797477)
          ·
            refine ⟨35373016005882794993962027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188656085364708239967797477 35373016005882794993962027)
            ·
              refine ⟨53059524008824192490943041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35373016005882794993962027 53059524008824192490943041)
              ·
                refine ⟨39794643006618144368207281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53059524008824192490943041 39794643006618144368207281)
                ·
                  refine ⟨29845982254963608276155461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39794643006618144368207281 29845982254963608276155461)
                  ·
                    refine ⟨5596121672805676551779149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29845982254963608276155461 5596121672805676551779149)
                    ·
                      refine ⟨2098545627302128706917181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5596121672805676551779149 2098545627302128706917181)
                      ·
                        rfl

theorem cell23_4086903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_4086903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086903 prefixEnd_4086903 := by exact prefixLift 4086903
  have htrace : WordTrace (prefixWord ++ tailWord_4086903) baseStart_4086903 baseEnd_4086903 := by
    simpa [prefixWord, tailWord_4086903, baseEnd_4086903] using wordTrace_append hprefix tailTrace_4086903
  have hstable : (prefixWord ++ tailWord_4086903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086903).length < 2 ^ (prefixWord ++ tailWord_4086903).sum := by decide
  have hdescent : baseEnd_4086903 < baseStart_4086903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086930 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_4086930 : Nat := 118140960795 + 4086930 * 2 ^ 59
def prefixEnd_4086930 : Nat := 4983230072969 + 3 ^ 40 * 4086930 * 2
def baseEnd_4086930 : Nat := 2098559491279800101279557

theorem tailTrace_4086930 : CollatzResearch.WordTrace tailWord_4086930 prefixEnd_4086930 2098559491279800101279557 := by
  unfold tailWord_4086930
  simp only [CollatzResearch.WordTrace]
  refine ⟨37265645770939519229780561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99375055389172051279414829 37265645770939519229780561)
  ·
    refine ⟨27949234328204639422335421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37265645770939519229780561 27949234328204639422335421)
    ·
      refine ⟨10480962873076739783375783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27949234328204639422335421 10480962873076739783375783)
      ·
        refine ⟨15721444309615109675063675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10480962873076739783375783 15721444309615109675063675)
        ·
          refine ⟨23582166464422664512595513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15721444309615109675063675 23582166464422664512595513)
          ·
            refine ⟨17686624848316998384446635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23582166464422664512595513 17686624848316998384446635)
            ·
              refine ⟨26529937272475497576669953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17686624848316998384446635 26529937272475497576669953)
              ·
                refine ⟨19897452954356623182502465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26529937272475497576669953 19897452954356623182502465)
                ·
                  refine ⟨14923089715767467386876849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19897452954356623182502465 14923089715767467386876849)
                  ·
                    refine ⟨11192317286825600540157637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14923089715767467386876849 11192317286825600540157637)
                    ·
                      refine ⟨2098559491279800101279557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11192317286825600540157637 2098559491279800101279557)
                      ·
                        rfl

theorem cell23_4086930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_4086930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086930 prefixEnd_4086930 := by exact prefixLift 4086930
  have htrace : WordTrace (prefixWord ++ tailWord_4086930) baseStart_4086930 baseEnd_4086930 := by
    simpa [prefixWord, tailWord_4086930, baseEnd_4086930] using wordTrace_append hprefix tailTrace_4086930
  have hstable : (prefixWord ++ tailWord_4086930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086930).length < 2 ^ (prefixWord ++ tailWord_4086930).sum := by decide
  have hdescent : baseEnd_4086930 < baseStart_4086930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086940 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 7]
def baseStart_4086940 : Nat := 118140960795 + 4086940 * 2 ^ 59
def prefixEnd_4086940 : Nat := 4983230072969 + 3 ^ 40 * 4086940 * 2
def baseEnd_4086940 : Nat := 233173847342927229128279

theorem tailTrace_4086940 : CollatzResearch.WordTrace tailWord_4086940 prefixEnd_4086940 233173847342927229128279 := by
  unfold tailWord_4086940
  simp only [CollatzResearch.WordTrace]
  refine ⟨74531473906860924313493137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99375298542481232417990849 74531473906860924313493137)
  ·
    refine ⟨55898605430145693235119853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74531473906860924313493137 55898605430145693235119853)
    ·
      refine ⟨20961977036304634963169945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55898605430145693235119853 20961977036304634963169945)
      ·
        refine ⟨15721482777228476222377459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20961977036304634963169945 15721482777228476222377459)
        ·
          refine ⟨23582224165842714333566189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15721482777228476222377459 23582224165842714333566189)
          ·
            refine ⟨8843334062191017875087321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23582224165842714333566189 8843334062191017875087321)
            ·
              refine ⟨6632500546643263406315491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8843334062191017875087321 6632500546643263406315491)
              ·
                refine ⟨9948750819964895109473237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632500546643263406315491 9948750819964895109473237)
                ·
                  refine ⟨233173847342927229128279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9948750819964895109473237 233173847342927229128279)
                  ·
                    rfl

theorem cell23_4086940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_4086940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086940 prefixEnd_4086940 := by exact prefixLift 4086940
  have htrace : WordTrace (prefixWord ++ tailWord_4086940) baseStart_4086940 baseEnd_4086940 := by
    simpa [prefixWord, tailWord_4086940, baseEnd_4086940] using wordTrace_append hprefix tailTrace_4086940
  have hstable : (prefixWord ++ tailWord_4086940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086940).length < 2 ^ (prefixWord ++ tailWord_4086940).sum := by decide
  have hdescent : baseEnd_4086940 < baseStart_4086940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086974 : List Nat := [4, 2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_4086974 : Nat := 118140960795 + 4086974 * 2 ^ 59
def prefixEnd_4086974 : Nat := 4983230072969 + 3 ^ 40 * 4086974 * 2
def baseEnd_4086974 : Nat := 233175787158733103236595

theorem tailTrace_4086974 : CollatzResearch.WordTrace tailWord_4086974 prefixEnd_4086974 233175787158733103236595 := by
  unfold tailWord_4086974
  simp only [CollatzResearch.WordTrace]
  refine ⟨18633023486949834054215497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99376125263732448289149317 18633023486949834054215497)
  ·
    refine ⟨13974767615212375540661623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18633023486949834054215497 13974767615212375540661623)
    ·
      refine ⟨20962151422818563310992435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13974767615212375540661623 20962151422818563310992435)
      ·
        refine ⟨31443227134227844966488653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20962151422818563310992435 31443227134227844966488653)
        ·
          refine ⟨11791210175335441862433245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31443227134227844966488653 11791210175335441862433245)
          ·
            refine ⟨4421703815750790698412467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11791210175335441862433245 4421703815750790698412467)
            ·
              refine ⟨6632555723626186047618701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421703815750790698412467 6632555723626186047618701)
              ·
                refine ⟨2487208396359819767857013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6632555723626186047618701 2487208396359819767857013)
                ·
                  refine ⟨233175787158733103236595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2487208396359819767857013 233175787158733103236595)
                  ·
                    rfl

theorem cell23_4086974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_4086974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086974 prefixEnd_4086974 := by exact prefixLift 4086974
  have htrace : WordTrace (prefixWord ++ tailWord_4086974) baseStart_4086974 baseEnd_4086974 := by
    simpa [prefixWord, tailWord_4086974, baseEnd_4086974] using wordTrace_append hprefix tailTrace_4086974
  have hstable : (prefixWord ++ tailWord_4086974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086974).length < 2 ^ (prefixWord ++ tailWord_4086974).sum := by decide
  have hdescent : baseEnd_4086974 < baseStart_4086974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087027 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 3]
def baseStart_4087027 : Nat := 118140960795 + 4087027 * 2 ^ 59
def prefixEnd_4087027 : Nat := 4983230072969 + 3 ^ 40 * 4087027 * 2
def baseEnd_4087027 : Nat := 2098609298903286221766611

theorem tailTrace_4087027 : CollatzResearch.WordTrace tailWord_4087027 prefixEnd_4087027 2098609298903286221766611 := by
  unfold tailWord_4087027
  simp only [CollatzResearch.WordTrace]
  refine ⟨149066120964406662485403335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99377413976271108323602223 149066120964406662485403335)
  ·
    refine ⟨223599181446609993728105003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149066120964406662485403335 223599181446609993728105003)
    ·
      refine ⟨335398772169914990592157505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223599181446609993728105003 335398772169914990592157505)
      ·
        refine ⟨251549079127436242944118129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335398772169914990592157505 251549079127436242944118129)
        ·
          refine ⟨188661809345577182208088597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251549079127436242944118129 188661809345577182208088597)
          ·
            refine ⟨8843522313073930416004153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188661809345577182208088597 8843522313073930416004153)
            ·
              refine ⟨6632641734805447812003115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8843522313073930416004153 6632641734805447812003115)
              ·
                refine ⟨9948962602208171718004673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632641734805447812003115 9948962602208171718004673)
                ·
                  refine ⟨7461721951656128788503505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9948962602208171718004673 7461721951656128788503505)
                  ·
                    refine ⟨5596291463742096591377629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7461721951656128788503505 5596291463742096591377629)
                    ·
                      refine ⟨2098609298903286221766611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5596291463742096591377629 2098609298903286221766611)
                      ·
                        rfl

theorem cell23_4087027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 3].length) (baseStart_4087027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087027 prefixEnd_4087027 := by exact prefixLift 4087027
  have htrace : WordTrace (prefixWord ++ tailWord_4087027) baseStart_4087027 baseEnd_4087027 := by
    simpa [prefixWord, tailWord_4087027, baseEnd_4087027] using wordTrace_append hprefix tailTrace_4087027
  have hstable : (prefixWord ++ tailWord_4087027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087027).length < 2 ^ (prefixWord ++ tailWord_4087027).sum := by decide
  have hdescent : baseEnd_4087027 < baseStart_4087027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087051 : List Nat := [1, 1, 1, 1, 5, 5, 2, 2, 1, 4]
def baseStart_4087051 : Nat := 118140960795 + 4087051 * 2 ^ 59
def prefixEnd_4087051 : Nat := 4983230072969 + 3 ^ 40 * 4087051 * 2
def baseEnd_4087051 : Nat := 699540540812998042622167

theorem tailTrace_4087051 : CollatzResearch.WordTrace tailWord_4087051 prefixEnd_4087051 699540540812998042622167 := by
  unfold tailWord_4087051
  simp only [CollatzResearch.WordTrace]
  refine ⟨149066996316319714584277007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99377997544213143056184671 149066996316319714584277007)
  ·
    refine ⟨223600494474479571876415511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149066996316319714584277007 223600494474479571876415511)
    ·
      refine ⟨335400741711719357814623267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223600494474479571876415511 335400741711719357814623267)
      ·
        refine ⟨503101112567579036721934901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335400741711719357814623267 503101112567579036721934901)
        ·
          refine ⟨47165729303210534692681397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 503101112567579036721934901 47165729303210534692681397)
          ·
            refine ⟨4421787122175987627438881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47165729303210534692681397 4421787122175987627438881)
            ·
              refine ⟨3316340341631990720579161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4421787122175987627438881 3316340341631990720579161)
              ·
                refine ⟨2487255256223993040434371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3316340341631990720579161 2487255256223993040434371)
                ·
                  refine ⟨3730882884335989560651557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487255256223993040434371 3730882884335989560651557)
                  ·
                    refine ⟨699540540812998042622167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3730882884335989560651557 699540540812998042622167)
                    ·
                      rfl

theorem cell23_4087051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 1, 4].length) (baseStart_4087051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087051 prefixEnd_4087051 := by exact prefixLift 4087051
  have htrace : WordTrace (prefixWord ++ tailWord_4087051) baseStart_4087051 baseEnd_4087051 := by
    simpa [prefixWord, tailWord_4087051, baseEnd_4087051] using wordTrace_append hprefix tailTrace_4087051
  have hstable : (prefixWord ++ tailWord_4087051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087051).length < 2 ^ (prefixWord ++ tailWord_4087051).sum := by decide
  have hdescent : baseEnd_4087051 < baseStart_4087051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087057 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 3, 1, 3]
def baseStart_4087057 : Nat := 118140960795 + 4087057 * 2 ^ 59
def prefixEnd_4087057 : Nat := 4983230072969 + 3 ^ 40 * 4087057 * 2
def baseEnd_4087057 : Nat := 2098624703322921104391473

theorem tailTrace_4087057 : CollatzResearch.WordTrace tailWord_4087057 prefixEnd_4087057 2098624703322921104391473 := by
  unfold tailWord_4087057
  simp only [CollatzResearch.WordTrace]
  refine ⟨149067215154297977608995425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99378143436198651739330283 149067215154297977608995425)
  ·
    refine ⟨111800411365723483206746569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149067215154297977608995425 111800411365723483206746569)
    ·
      refine ⟨83850308524292612405059927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111800411365723483206746569 83850308524292612405059927)
      ·
        refine ⟨125775462786438918607589891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83850308524292612405059927 125775462786438918607589891)
        ·
          refine ⟨188663194179658377911384837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125775462786438918607589891 188663194179658377911384837)
          ·
            refine ⟨35374348908685945858384657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188663194179658377911384837 35374348908685945858384657)
            ·
              refine ⟨26530761681514459393788493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35374348908685945858384657 26530761681514459393788493)
              ·
                refine ⟨9949035630567922272670685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26530761681514459393788493 9949035630567922272670685)
                ·
                  refine ⟨3730888361462970852251507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9949035630567922272670685 3730888361462970852251507)
                  ·
                    refine ⟨5596332542194456278377261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3730888361462970852251507 5596332542194456278377261)
                    ·
                      refine ⟨2098624703322921104391473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5596332542194456278377261 2098624703322921104391473)
                      ·
                        rfl

theorem cell23_4087057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_4087057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087057 prefixEnd_4087057 := by exact prefixLift 4087057
  have htrace : WordTrace (prefixWord ++ tailWord_4087057) baseStart_4087057 baseEnd_4087057 := by
    simpa [prefixWord, tailWord_4087057, baseEnd_4087057] using wordTrace_append hprefix tailTrace_4087057
  have hstable : (prefixWord ++ tailWord_4087057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087057).length < 2 ^ (prefixWord ++ tailWord_4087057).sum := by decide
  have hdescent : baseEnd_4087057 < baseStart_4087057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087091 : List Nat := [1, 1, 1, 2, 5, 3, 2, 3, 1, 1, 3]
def baseStart_4087091 : Nat := 118140960795 + 4087091 * 2 ^ 59
def prefixEnd_4087091 : Nat := 4983230072969 + 3 ^ 40 * 4087091 * 2
def baseEnd_4087091 : Nat := 2098642161665173971366317

theorem tailTrace_4087091 : CollatzResearch.WordTrace tailWord_4087091 prefixEnd_4087091 2098642161665173971366317 := by
  unfold tailWord_4087091
  simp only [CollatzResearch.WordTrace]
  refine ⟨149068455236174801415733127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99378970157449867610488751 149068455236174801415733127)
  ·
    refine ⟨223602682854262202123599691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149068455236174801415733127 223602682854262202123599691)
    ·
      refine ⟨335404024281393303185399537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223602682854262202123599691 335404024281393303185399537)
      ·
        refine ⟨251553018211044977389049653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335404024281393303185399537 251553018211044977389049653)
        ·
          refine ⟨23583095457285466630223405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251553018211044977389049653 23583095457285466630223405)
          ·
            refine ⟨8843660796482049986333777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23583095457285466630223405 8843660796482049986333777)
            ·
              refine ⟨6632745597361537489750333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8843660796482049986333777 6632745597361537489750333)
              ·
                refine ⟨2487279599010576558656375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6632745597361537489750333 2487279599010576558656375)
                ·
                  refine ⟨3730919398515864837984563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487279599010576558656375 3730919398515864837984563)
                  ·
                    refine ⟨5596379097773797256976845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3730919398515864837984563 5596379097773797256976845)
                    ·
                      refine ⟨2098642161665173971366317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5596379097773797256976845 2098642161665173971366317)
                      ·
                        rfl

theorem cell23_4087091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 1, 1, 3].length) (baseStart_4087091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087091 prefixEnd_4087091 := by exact prefixLift 4087091
  have htrace : WordTrace (prefixWord ++ tailWord_4087091) baseStart_4087091 baseEnd_4087091 := by
    simpa [prefixWord, tailWord_4087091, baseEnd_4087091] using wordTrace_append hprefix tailTrace_4087091
  have hstable : (prefixWord ++ tailWord_4087091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087091).length < 2 ^ (prefixWord ++ tailWord_4087091).sum := by decide
  have hdescent : baseEnd_4087091 < baseStart_4087091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087108 : List Nat := [2, 3, 4, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_4087108 : Nat := 118140960795 + 4087108 * 2 ^ 59
def prefixEnd_4087108 : Nat := 4983230072969 + 3 ^ 40 * 4087108 * 2
def baseEnd_4087108 : Nat := 2098650890836300404853739

theorem tailTrace_4087108 : CollatzResearch.WordTrace tailWord_4087108 prefixEnd_4087108 2098650890836300404853739 := by
  unfold tailWord_4087108
  simp only [CollatzResearch.WordTrace]
  refine ⟨74534537638556606659550989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99379383518075475546067985 74534537638556606659550989)
  ·
    refine ⟨27950451614458727497331621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74534537638556606659550989 27950451614458727497331621)
    ·
      refine ⟨5240709677711011405749679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27950451614458727497331621 5240709677711011405749679)
      ·
        refine ⟨7861064516566517108624519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5240709677711011405749679 7861064516566517108624519)
        ·
          refine ⟨11791596774849775662936779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7861064516566517108624519 11791596774849775662936779)
          ·
            refine ⟨17687395162274663494405169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11791596774849775662936779 17687395162274663494405169)
            ·
              refine ⟨13265546371705997620803877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17687395162274663494405169 13265546371705997620803877)
              ·
                refine ⟨2487289944694874553900727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13265546371705997620803877 2487289944694874553900727)
                ·
                  refine ⟨3730934917042311830851091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487289944694874553900727 3730934917042311830851091)
                  ·
                    refine ⟨5596402375563467746276637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3730934917042311830851091 5596402375563467746276637)
                    ·
                      refine ⟨2098650890836300404853739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5596402375563467746276637 2098650890836300404853739)
                      ·
                        rfl

theorem cell23_4087108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_4087108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087108 prefixEnd_4087108 := by exact prefixLift 4087108
  have htrace : WordTrace (prefixWord ++ tailWord_4087108) baseStart_4087108 baseEnd_4087108 := by
    simpa [prefixWord, tailWord_4087108, baseEnd_4087108] using wordTrace_append hprefix tailTrace_4087108
  have hstable : (prefixWord ++ tailWord_4087108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087108).length < 2 ^ (prefixWord ++ tailWord_4087108).sum := by decide
  have hdescent : baseEnd_4087108 < baseStart_4087108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087127 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 4]
def baseStart_4087127 : Nat := 118140960795 + 4087127 * 2 ^ 59
def prefixEnd_4087127 : Nat := 4983230072969 + 3 ^ 40 * 4087127 * 2
def baseEnd_4087127 : Nat := 2098660646968735830516151

theorem tailTrace_4087127 : CollatzResearch.WordTrace tailWord_4087127 prefixEnd_4087127 2098660646968735830516151 := by
  unfold tailWord_4087127
  simp only [CollatzResearch.WordTrace]
  refine ⟨149069768264044379564043635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99379845509362919709362423 149069768264044379564043635)
  ·
    refine ⟨223604652396066569346065453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149069768264044379564043635 223604652396066569346065453)
    ·
      refine ⟨83851744648524963504774545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223604652396066569346065453 83851744648524963504774545)
      ·
        refine ⟨62888808486393722628580909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83851744648524963504774545 62888808486393722628580909)
        ·
          refine ⟨23583303182397645985717841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62888808486393722628580909 23583303182397645985717841)
          ·
            refine ⟨17687477386798234489288381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23583303182397645985717841 17687477386798234489288381)
            ·
              refine ⟨6632804020049337933483143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17687477386798234489288381 6632804020049337933483143)
              ·
                refine ⟨9949206030074006900224715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632804020049337933483143 9949206030074006900224715)
                ·
                  refine ⟨14923809045111010350337073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9949206030074006900224715 14923809045111010350337073)
                  ·
                    refine ⟨11192856783833257762752805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14923809045111010350337073 11192856783833257762752805)
                    ·
                      refine ⟨2098660646968735830516151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11192856783833257762752805 2098660646968735830516151)
                      ·
                        rfl

theorem cell23_4087127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_4087127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087127 prefixEnd_4087127 := by exact prefixLift 4087127
  have htrace : WordTrace (prefixWord ++ tailWord_4087127) baseStart_4087127 baseEnd_4087127 := by
    simpa [prefixWord, tailWord_4087127, baseEnd_4087127] using wordTrace_append hprefix tailTrace_4087127
  have hstable : (prefixWord ++ tailWord_4087127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087127).length < 2 ^ (prefixWord ++ tailWord_4087127).sum := by decide
  have hdescent : baseEnd_4087127 < baseStart_4087127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087148 : List Nat := [2, 2, 1, 1, 5, 1, 3, 3, 1, 2, 2]
def baseStart_4087148 : Nat := 118140960795 + 4087148 * 2 ^ 59
def prefixEnd_4087148 : Nat := 4983230072969 + 3 ^ 40 * 4087148 * 2
def baseEnd_4087148 : Nat := 2098671430062480248353555

theorem tailTrace_4087148 : CollatzResearch.WordTrace tailWord_4087148 prefixEnd_4087148 2098671430062480248353555 := by
  unfold tailWord_4087148
  simp only [CollatzResearch.WordTrace]
  refine ⟨74535267098484150075279049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99380356131312200100372065 74535267098484150075279049)
  ·
    refine ⟨55901450323863112556459287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74535267098484150075279049 55901450323863112556459287)
    ·
      refine ⟨83852175485794668834688931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55901450323863112556459287 83852175485794668834688931)
      ·
        refine ⟨125778263228692003252033397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83852175485794668834688931 125778263228692003252033397)
        ·
          refine ⟨11791712177689875304878131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125778263228692003252033397 11791712177689875304878131)
          ·
            refine ⟨17687568266534812957317197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11791712177689875304878131 17687568266534812957317197)
            ·
              refine ⟨6632838099950554858993949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17687568266534812957317197 6632838099950554858993949)
              ·
                refine ⟨2487314287481458072122731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6632838099950554858993949 2487314287481458072122731)
                ·
                  refine ⟨3730971431222187108184097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487314287481458072122731 3730971431222187108184097)
                  ·
                    refine ⟨2798228573416640331138073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3730971431222187108184097 2798228573416640331138073)
                    ·
                      refine ⟨2098671430062480248353555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2798228573416640331138073 2098671430062480248353555)
                      ·
                        rfl

theorem cell23_4087148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 1, 2, 2].length) (baseStart_4087148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087148 prefixEnd_4087148 := by exact prefixLift 4087148
  have htrace : WordTrace (prefixWord ++ tailWord_4087148) baseStart_4087148 baseEnd_4087148 := by
    simpa [prefixWord, tailWord_4087148, baseEnd_4087148] using wordTrace_append hprefix tailTrace_4087148
  have hstable : (prefixWord ++ tailWord_4087148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087148).length < 2 ^ (prefixWord ++ tailWord_4087148).sum := by decide
  have hdescent : baseEnd_4087148 < baseStart_4087148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087164 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_4087164 : Nat := 118140960795 + 4087164 * 2 ^ 59
def prefixEnd_4087164 : Nat := 4983230072969 + 3 ^ 40 * 4087164 * 2
def baseEnd_4087164 : Nat := 2098679645752952185753481

theorem tailTrace_4087164 : CollatzResearch.WordTrace tailWord_4087164 prefixEnd_4087164 2098679645752952185753481 := by
  unfold tailWord_4087164
  simp only [CollatzResearch.WordTrace]
  refine ⟨74535558882455167441570273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99380745176606889922093697 74535558882455167441570273)
  ·
    refine ⟨55901669161841375581177705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74535558882455167441570273 55901669161841375581177705)
    ·
      refine ⟨41926251871381031685883279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55901669161841375581177705 41926251871381031685883279)
      ·
        refine ⟨62889377807071547528824919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41926251871381031685883279 62889377807071547528824919)
        ·
          refine ⟨94334066710607321293237379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62889377807071547528824919 94334066710607321293237379)
          ·
            refine ⟨141501100065910981939856069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94334066710607321293237379 141501100065910981939856069)
            ·
              refine ⟨26531456262358309113723013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141501100065910981939856069 26531456262358309113723013)
              ·
                refine ⟨4974648049192182958823065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26531456262358309113723013 4974648049192182958823065)
                ·
                  refine ⟨3730986036894137219117299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4974648049192182958823065 3730986036894137219117299)
                  ·
                    refine ⟨5596479055341205828675949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3730986036894137219117299 5596479055341205828675949)
                    ·
                      refine ⟨2098679645752952185753481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5596479055341205828675949 2098679645752952185753481)
                      ·
                        rfl

theorem cell23_4087164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_4087164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087164 prefixEnd_4087164 := by exact prefixLift 4087164
  have htrace : WordTrace (prefixWord ++ tailWord_4087164) baseStart_4087164 baseEnd_4087164 := by
    simpa [prefixWord, tailWord_4087164, baseEnd_4087164] using wordTrace_append hprefix tailTrace_4087164
  have hstable : (prefixWord ++ tailWord_4087164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087164).length < 2 ^ (prefixWord ++ tailWord_4087164).sum := by decide
  have hdescent : baseEnd_4087164 < baseStart_4087164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087180 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_4087180 : Nat := 118140960795 + 4087180 * 2 ^ 59
def prefixEnd_4087180 : Nat := 4983230072969 + 3 ^ 40 * 4087180 * 2
def baseEnd_4087180 : Nat := 699562620481141374384469

theorem tailTrace_4087180 : CollatzResearch.WordTrace tailWord_4087180 prefixEnd_4087180 699562620481141374384469 := by
  unfold tailWord_4087180
  simp only [CollatzResearch.WordTrace]
  refine ⟨74535850666426184807861497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99381134221901579743815329 74535850666426184807861497)
  ·
    refine ⟨55901887999819638605896123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74535850666426184807861497 55901887999819638605896123)
    ·
      refine ⟨83852831999729457908844185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55901887999819638605896123 83852831999729457908844185)
      ·
        refine ⟨62889623999797093431633139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83852831999729457908844185 62889623999797093431633139)
        ·
          refine ⟨94334435999695640147449709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62889623999797093431633139 94334435999695640147449709)
          ·
            refine ⟨35375413499885865055293641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94334435999695640147449709 35375413499885865055293641)
            ·
              refine ⟨26531560124914398791470231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35375413499885865055293641 26531560124914398791470231)
              ·
                refine ⟨39797340187371598187205347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26531560124914398791470231 39797340187371598187205347)
                ·
                  refine ⟨59696010281057397280808021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39797340187371598187205347 59696010281057397280808021)
                  ·
                    refine ⟨699562620481141374384469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59696010281057397280808021 699562620481141374384469)
                    ·
                      rfl

theorem cell23_4087180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_4087180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087180 prefixEnd_4087180 := by exact prefixLift 4087180
  have htrace : WordTrace (prefixWord ++ tailWord_4087180) baseStart_4087180 baseEnd_4087180 := by
    simpa [prefixWord, tailWord_4087180, baseEnd_4087180] using wordTrace_append hprefix tailTrace_4087180
  have hstable : (prefixWord ++ tailWord_4087180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087180).length < 2 ^ (prefixWord ++ tailWord_4087180).sum := by decide
  have hdescent : baseEnd_4087180 < baseStart_4087180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087187 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 7, 4, 2]
def baseStart_4087187 : Nat := 118140960795 + 4087187 * 2 ^ 59
def prefixEnd_4087187 : Nat := 4983230072969 + 3 ^ 40 * 4087187 * 2
def baseEnd_4087187 : Nat := 2098691455808005595765875

theorem tailTrace_4087187 : CollatzResearch.WordTrace tailWord_4087187 prefixEnd_4087187 2098691455808005595765875 := by
  unfold tailWord_4087187
  simp only [CollatzResearch.WordTrace]
  refine ⟨149071956643827009811227815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99381304429218006540818543 149071956643827009811227815)
  ·
    refine ⟨223607934965740514716841723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149071956643827009811227815 223607934965740514716841723)
    ·
      refine ⟨335411902448610772075262585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223607934965740514716841723 335411902448610772075262585)
      ·
        refine ⟨251558926836458079056446939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335411902448610772075262585 251558926836458079056446939)
        ·
          refine ⟨377338390254687118584670409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251558926836458079056446939 377338390254687118584670409)
          ·
            refine ⟨283003792691015338938502807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377338390254687118584670409 283003792691015338938502807)
            ·
              refine ⟨424505689036523008407754211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283003792691015338938502807 424505689036523008407754211)
              ·
                refine ⟨636758533554784512611631317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424505689036523008407754211 636758533554784512611631317)
                ·
                  refine ⟨14924028130190262014335109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 636758533554784512611631317 14924028130190262014335109)
                  ·
                    refine ⟨2798255274410674127687833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14924028130190262014335109 2798255274410674127687833)
                    ·
                      refine ⟨2098691455808005595765875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2798255274410674127687833 2098691455808005595765875)
                      ·
                        rfl

theorem cell23_4087187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 4, 2].length) (baseStart_4087187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087187 prefixEnd_4087187 := by exact prefixLift 4087187
  have htrace : WordTrace (prefixWord ++ tailWord_4087187) baseStart_4087187 baseEnd_4087187 := by
    simpa [prefixWord, tailWord_4087187, baseEnd_4087187] using wordTrace_append hprefix tailTrace_4087187
  have hstable : (prefixWord ++ tailWord_4087187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087187).length < 2 ^ (prefixWord ++ tailWord_4087187).sum := by decide
  have hdescent : baseEnd_4087187 < baseStart_4087187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087207 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4087207 : Nat := 118140960795 + 4087207 * 2 ^ 59
def prefixEnd_4087207 : Nat := 4983230072969 + 3 ^ 40 * 4087207 * 2
def baseEnd_4087207 : Nat := 2098701725421095517515783

theorem tailTrace_4087207 : CollatzResearch.WordTrace tailWord_4087207 prefixEnd_4087207 2098701725421095517515783 := by
  unfold tailWord_4087207
  simp only [CollatzResearch.WordTrace]
  refine ⟨149072686103754553226955875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99381790735836368817970583 149072686103754553226955875)
  ·
    refine ⟨223609029155631829840433813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149072686103754553226955875 223609029155631829840433813)
    ·
      refine ⟨10481673241670242023770335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 223609029155631829840433813 10481673241670242023770335)
      ·
        refine ⟨15722509862505363035655503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10481673241670242023770335 15722509862505363035655503)
        ·
          refine ⟨23583764793758044553483255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15722509862505363035655503 23583764793758044553483255)
          ·
            refine ⟨35375647190637066830224883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23583764793758044553483255 35375647190637066830224883)
            ·
              refine ⟨53063470785955600245337325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35375647190637066830224883 53063470785955600245337325)
              ·
                refine ⟨19898801544733350092001497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53063470785955600245337325 19898801544733350092001497)
                ·
                  refine ⟨14924101158550012569001123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19898801544733350092001497 14924101158550012569001123)
                  ·
                    refine ⟨22386151737825018853501685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14924101158550012569001123 22386151737825018853501685)
                    ·
                      refine ⟨2098701725421095517515783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22386151737825018853501685 2098701725421095517515783)
                      ·
                        rfl

theorem cell23_4087207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4087207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087207 prefixEnd_4087207 := by exact prefixLift 4087207
  have htrace : WordTrace (prefixWord ++ tailWord_4087207) baseStart_4087207 baseEnd_4087207 := by
    simpa [prefixWord, tailWord_4087207, baseEnd_4087207] using wordTrace_append hprefix tailTrace_4087207
  have hstable : (prefixWord ++ tailWord_4087207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087207).length < 2 ^ (prefixWord ++ tailWord_4087207).sum := by decide
  have hdescent : baseEnd_4087207 < baseStart_4087207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087217 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4087217 : Nat := 118140960795 + 4087217 * 2 ^ 59
def prefixEnd_4087217 : Nat := 4983230072969 + 3 ^ 40 * 4087217 * 2
def baseEnd_4087217 : Nat := 2098706860227640478390737

theorem tailTrace_4087217 : CollatzResearch.WordTrace tailWord_4087217 prefixEnd_4087217 2098706860227640478390737 := by
  unfold tailWord_4087217
  simp only [CollatzResearch.WordTrace]
  refine ⟨149073050833718324934819905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99382033889145549956546603 149073050833718324934819905)
  ·
    refine ⟨111804788125288743701114929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149073050833718324934819905 111804788125288743701114929)
    ·
      refine ⟨83853591093966557775836197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111804788125288743701114929 83853591093966557775836197)
      ·
        refine ⟨15722548330118729582969287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83853591093966557775836197 15722548330118729582969287)
        ·
          refine ⟨23583822495178094374453931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15722548330118729582969287 23583822495178094374453931)
          ·
            refine ⟨35375733742767141561680897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23583822495178094374453931 35375733742767141561680897)
            ·
              refine ⟨26531800307075356171260673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35375733742767141561680897 26531800307075356171260673)
              ·
                refine ⟨19898850230306517128445505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26531800307075356171260673 19898850230306517128445505)
                ·
                  refine ⟨14924137672729887846334129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19898850230306517128445505 14924137672729887846334129)
                  ·
                    refine ⟨11193103254547415884750597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14924137672729887846334129 11193103254547415884750597)
                    ·
                      refine ⟨2098706860227640478390737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11193103254547415884750597 2098706860227640478390737)
                      ·
                        rfl

theorem cell23_4087217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4087217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087217 prefixEnd_4087217 := by exact prefixLift 4087217
  have htrace : WordTrace (prefixWord ++ tailWord_4087217) baseStart_4087217 baseEnd_4087217 := by
    simpa [prefixWord, tailWord_4087217, baseEnd_4087217] using wordTrace_append hprefix tailTrace_4087217
  have hstable : (prefixWord ++ tailWord_4087217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087217).length < 2 ^ (prefixWord ++ tailWord_4087217).sum := by decide
  have hdescent : baseEnd_4087217 < baseStart_4087217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087257 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 1, 7]
def baseStart_4087257 : Nat := 118140960795 + 4087257 * 2 ^ 59
def prefixEnd_4087257 : Nat := 4983230072969 + 3 ^ 40 * 4087257 * 2
def baseEnd_4087257 : Nat := 699575799817940107296851

theorem tailTrace_4087257 : CollatzResearch.WordTrace tailWord_4087257 prefixEnd_4087257 699575799817940107296851 := by
  unfold tailWord_4087257
  simp only [CollatzResearch.WordTrace]
  refine ⟨149074509753573411766276025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99383006502382274510850683 149074509753573411766276025)
  ·
    refine ⟨111805882315180058824707019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149074509753573411766276025 111805882315180058824707019)
    ·
      refine ⟨167708823472770088237060529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111805882315180058824707019 167708823472770088237060529)
      ·
        refine ⟨125781617604577566177795397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167708823472770088237060529 125781617604577566177795397)
        ·
          refine ⟨23584053300858293658336637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125781617604577566177795397 23584053300858293658336637)
          ·
            refine ⟨8844019987821860121876239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23584053300858293658336637 8844019987821860121876239)
            ·
              refine ⟨13266029981732790182814359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8844019987821860121876239 13266029981732790182814359)
              ·
                refine ⟨19899044972599185274221539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13266029981732790182814359 19899044972599185274221539)
                ·
                  refine ⟨29848567458898777911332309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19899044972599185274221539 29848567458898777911332309)
                  ·
                    refine ⟨699575799817940107296851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29848567458898777911332309 699575799817940107296851)
                    ·
                      rfl

theorem cell23_4087257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_4087257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087257 prefixEnd_4087257 := by exact prefixLift 4087257
  have htrace : WordTrace (prefixWord ++ tailWord_4087257) baseStart_4087257 baseEnd_4087257 := by
    simpa [prefixWord, tailWord_4087257, baseEnd_4087257] using wordTrace_append hprefix tailTrace_4087257
  have hstable : (prefixWord ++ tailWord_4087257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087257).length < 2 ^ (prefixWord ++ tailWord_4087257).sum := by decide
  have hdescent : baseEnd_4087257 < baseStart_4087257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087261 : List Nat := [1, 4, 3, 1, 1, 3, 2, 3, 5]
def baseStart_4087261 : Nat := 118140960795 + 4087261 * 2 ^ 59
def prefixEnd_4087261 : Nat := 4983230072969 + 3 ^ 40 * 4087261 * 2
def baseEnd_4087261 : Nat := 233192161486270922915615

theorem tailTrace_4087261 : CollatzResearch.WordTrace tailWord_4087261 prefixEnd_4087261 233192161486270922915615 := by
  unfold tailWord_4087261
  simp only [CollatzResearch.WordTrace]
  refine ⟨149074655645558920449421637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99383103763705946966281091 149074655645558920449421637)
  ·
    refine ⟨27951497933542297584266557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149074655645558920449421637 27951497933542297584266557)
    ·
      refine ⟨10481811725078361594099959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27951497933542297584266557 10481811725078361594099959)
      ·
        refine ⟨15722717587617542391149939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10481811725078361594099959 15722717587617542391149939)
        ·
          refine ⟨23584076381426313586724909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15722717587617542391149939 23584076381426313586724909)
          ·
            refine ⟨8844028643034867595021841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23584076381426313586724909 8844028643034867595021841)
            ·
              refine ⟨6633021482276150696266381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8844028643034867595021841 6633021482276150696266381)
              ·
                refine ⟨2487383055853556511099893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6633021482276150696266381 2487383055853556511099893)
                ·
                  refine ⟨233192161486270922915615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2487383055853556511099893 233192161486270922915615)
                  ·
                    rfl

theorem cell23_4087261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_4087261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087261 prefixEnd_4087261 := by exact prefixLift 4087261
  have htrace : WordTrace (prefixWord ++ tailWord_4087261) baseStart_4087261 baseEnd_4087261 := by
    simpa [prefixWord, tailWord_4087261, baseEnd_4087261] using wordTrace_append hprefix tailTrace_4087261
  have hstable : (prefixWord ++ tailWord_4087261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087261).length < 2 ^ (prefixWord ++ tailWord_4087261).sum := by decide
  have hdescent : baseEnd_4087261 < baseStart_4087261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087304 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 3, 4]
def baseStart_4087304 : Nat := 118140960795 + 4087304 * 2 ^ 59
def prefixEnd_4087304 : Nat := 4983230072969 + 3 ^ 40 * 4087304 * 2
def baseEnd_4087304 : Nat := 699583844348193879334279

theorem tailTrace_4087304 : CollatzResearch.WordTrace tailWord_4087304 prefixEnd_4087304 699583844348193879334279 := by
  unfold tailWord_4087304
  simp only [CollatzResearch.WordTrace]
  refine ⟨74538111992201569396618483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99384149322935425862157977 74538111992201569396618483)
  ·
    refine ⟨111807167988302354094927725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74538111992201569396618483 111807167988302354094927725)
    ·
      refine ⟨41927687995613382785597897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111807167988302354094927725 41927687995613382785597897)
      ·
        refine ⟨31445765996710037089198423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41927687995613382785597897 31445765996710037089198423)
        ·
          refine ⟨47168648995065055633797635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31445765996710037089198423 47168648995065055633797635)
          ·
            refine ⟨70752973492597583450696453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47168648995065055633797635 70752973492597583450696453)
            ·
              refine ⟨13266182529862046897005585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70752973492597583450696453 13266182529862046897005585)
              ·
                refine ⟨9949636897396535172754189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13266182529862046897005585 9949636897396535172754189)
                ·
                  refine ⟨3731113836523700689782821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9949636897396535172754189 3731113836523700689782821)
                  ·
                    refine ⟨699583844348193879334279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3731113836523700689782821 699583844348193879334279)
                    ·
                      rfl

theorem cell23_4087304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_4087304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087304 prefixEnd_4087304 := by exact prefixLift 4087304
  have htrace : WordTrace (prefixWord ++ tailWord_4087304) baseStart_4087304 baseEnd_4087304 := by
    simpa [prefixWord, tailWord_4087304, baseEnd_4087304] using wordTrace_append hprefix tailTrace_4087304
  have hstable : (prefixWord ++ tailWord_4087304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087304).length < 2 ^ (prefixWord ++ tailWord_4087304).sum := by decide
  have hdescent : baseEnd_4087304 < baseStart_4087304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087317 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 8]
def baseStart_4087317 : Nat := 118140960795 + 4087317 * 2 ^ 59
def prefixEnd_4087317 : Nat := 4983230072969 + 3 ^ 40 * 4087317 * 2
def baseEnd_4087317 : Nat := 233195356477010009682253

theorem tailTrace_4087317 : CollatzResearch.WordTrace tailWord_4087317 prefixEnd_4087317 233195356477010009682253 := by
  unfold tailWord_4087317
  simp only [CollatzResearch.WordTrace]
  refine ⟨149076698133356042013460205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99384465422237361342306803 149076698133356042013460205)
  ·
    refine ⟨55903761800008515755047577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149076698133356042013460205 55903761800008515755047577)
    ·
      refine ⟨41927821350006386816285683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55903761800008515755047577 41927821350006386816285683)
      ·
        refine ⟨62891732025009580224428525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41927821350006386816285683 62891732025009580224428525)
        ·
          refine ⟨23584399509378592584160697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62891732025009580224428525 23584399509378592584160697)
          ·
            refine ⟨17688299632033944438120523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23584399509378592584160697 17688299632033944438120523)
            ·
              refine ⟨26532449448050916657180785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17688299632033944438120523 26532449448050916657180785)
              ·
                refine ⟨19899337086038187492885589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26532449448050916657180785 19899337086038187492885589)
                ·
                  refine ⟨233195356477010009682253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19899337086038187492885589 233195356477010009682253)
                  ·
                    rfl

theorem cell23_4087317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_4087317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087317 prefixEnd_4087317 := by exact prefixLift 4087317
  have htrace : WordTrace (prefixWord ++ tailWord_4087317) baseStart_4087317 baseEnd_4087317 := by
    simpa [prefixWord, tailWord_4087317, baseEnd_4087317] using wordTrace_append hprefix tailTrace_4087317
  have hstable : (prefixWord ++ tailWord_4087317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087317).length < 2 ^ (prefixWord ++ tailWord_4087317).sum := by decide
  have hdescent : baseEnd_4087317 < baseStart_4087317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087331 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 3]
def baseStart_4087331 : Nat := 118140960795 + 4087331 * 2 ^ 59
def prefixEnd_4087331 : Nat := 4983230072969 + 3 ^ 40 * 4087331 * 2
def baseEnd_4087331 : Nat := 2098765397022253032365213

theorem tailTrace_4087331 : CollatzResearch.WordTrace tailWord_4087331 prefixEnd_4087331 2098765397022253032365213 := by
  unfold tailWord_4087331
  simp only [CollatzResearch.WordTrace]
  refine ⟨149077208755305322404469847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99384805836870214936313231 149077208755305322404469847)
  ·
    refine ⟨223615813132957983606704771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149077208755305322404469847 223615813132957983606704771)
    ·
      refine ⟨335423719699436975410057157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223615813132957983606704771 335423719699436975410057157)
      ·
        refine ⟨62891947443644432889385717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335423719699436975410057157 62891947443644432889385717)
        ·
          refine ⟨5896120072841665583379911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62891947443644432889385717 5896120072841665583379911)
          ·
            refine ⟨8844180109262498375069867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896120072841665583379911 8844180109262498375069867)
            ·
              refine ⟨13266270163893747562604801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8844180109262498375069867 13266270163893747562604801)
              ·
                refine ⟨9949702622920310671953601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13266270163893747562604801 9949702622920310671953601)
                ·
                  refine ⟨7462276967190233003965201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9949702622920310671953601 7462276967190233003965201)
                  ·
                    refine ⟨5596707725392674752973901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7462276967190233003965201 5596707725392674752973901)
                    ·
                      refine ⟨2098765397022253032365213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5596707725392674752973901 2098765397022253032365213)
                      ·
                        rfl

theorem cell23_4087331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_4087331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087331 prefixEnd_4087331 := by exact prefixLift 4087331
  have htrace : WordTrace (prefixWord ++ tailWord_4087331) baseStart_4087331 baseEnd_4087331 := by
    simpa [prefixWord, tailWord_4087331, baseEnd_4087331] using wordTrace_append hprefix tailTrace_4087331
  have hstable : (prefixWord ++ tailWord_4087331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087331).length < 2 ^ (prefixWord ++ tailWord_4087331).sum := by decide
  have hdescent : baseEnd_4087331 < baseStart_4087331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087351 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 6]
def baseStart_4087351 : Nat := 118140960795 + 4087351 * 2 ^ 59
def prefixEnd_4087351 : Nat := 4983230072969 + 3 ^ 40 * 4087351 * 2
def baseEnd_4087351 : Nat := 233197296292815883790569

theorem tailTrace_4087351 : CollatzResearch.WordTrace tailWord_4087351 prefixEnd_4087351 233197296292815883790569 := by
  unfold tailWord_4087351
  simp only [CollatzResearch.WordTrace]
  refine ⟨149077938215232865820197907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99385292143488577213465271 149077938215232865820197907)
  ·
    refine ⟨223616907322849298730296861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149077938215232865820197907 223616907322849298730296861)
    ·
      refine ⟨83856340246068487023861323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223616907322849298730296861 83856340246068487023861323)
      ·
        refine ⟨125784510369102730535791985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83856340246068487023861323 125784510369102730535791985)
        ·
          refine ⟨94338382776827047901843989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125784510369102730535791985 94338382776827047901843989)
          ·
            refine ⟨4422111692663767870398937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94338382776827047901843989 4422111692663767870398937)
            ·
              refine ⟨3316583769497825902799203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4422111692663767870398937 3316583769497825902799203)
              ·
                refine ⟨4974875654246738854198805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316583769497825902799203 4974875654246738854198805)
                ·
                  refine ⟨233197296292815883790569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4974875654246738854198805 233197296292815883790569)
                  ·
                    rfl

theorem cell23_4087351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 6].length) (baseStart_4087351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087351 prefixEnd_4087351 := by exact prefixLift 4087351
  have htrace : WordTrace (prefixWord ++ tailWord_4087351) baseStart_4087351 baseEnd_4087351 := by
    simpa [prefixWord, tailWord_4087351, baseEnd_4087351] using wordTrace_append hprefix tailTrace_4087351
  have hstable : (prefixWord ++ tailWord_4087351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087351).length < 2 ^ (prefixWord ++ tailWord_4087351).sum := by decide
  have hdescent : baseEnd_4087351 < baseStart_4087351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087361 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_4087361 : Nat := 118140960795 + 4087361 * 2 ^ 59
def prefixEnd_4087361 : Nat := 4983230072969 + 3 ^ 40 * 4087361 * 2
def baseEnd_4087361 : Nat := 2098780801441887914990075

theorem tailTrace_4087361 : CollatzResearch.WordTrace tailWord_4087361 prefixEnd_4087361 2098780801441887914990075 := by
  unfold tailWord_4087361
  simp only [CollatzResearch.WordTrace]
  refine ⟨149078302945196637528061937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99385535296797758352041291 149078302945196637528061937)
  ·
    refine ⟨111808727208897478146046453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149078302945196637528061937 111808727208897478146046453)
    ·
      refine ⟨10482068175834138576191855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111808727208897478146046453 10482068175834138576191855)
      ·
        refine ⟨15723102263751207864287783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10482068175834138576191855 15723102263751207864287783)
        ·
          refine ⟨23584653395626811796431675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15723102263751207864287783 23584653395626811796431675)
          ·
            refine ⟨35376980093440217694647513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23584653395626811796431675 35376980093440217694647513)
            ·
              refine ⟨26532735070080163270985635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35376980093440217694647513 26532735070080163270985635)
              ·
                refine ⟨39799102605120244906478453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26532735070080163270985635 39799102605120244906478453)
                ·
                  refine ⟨3731165869230022959982355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39799102605120244906478453 3731165869230022959982355)
                  ·
                    refine ⟨5596748803845034439973533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3731165869230022959982355 5596748803845034439973533)
                    ·
                      refine ⟨2098780801441887914990075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5596748803845034439973533 2098780801441887914990075)
                      ·
                        rfl

theorem cell23_4087361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_4087361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087361 prefixEnd_4087361 := by exact prefixLift 4087361
  have htrace : WordTrace (prefixWord ++ tailWord_4087361) baseStart_4087361 baseEnd_4087361 := by
    simpa [prefixWord, tailWord_4087361, baseEnd_4087361] using wordTrace_append hprefix tailTrace_4087361
  have hstable : (prefixWord ++ tailWord_4087361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087361).length < 2 ^ (prefixWord ++ tailWord_4087361).sum := by decide
  have hdescent : baseEnd_4087361 < baseStart_4087361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087388 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_4087388 : Nat := 118140960795 + 4087388 * 2 ^ 59
def prefixEnd_4087388 : Nat := 4983230072969 + 3 ^ 40 * 4087388 * 2
def baseEnd_4087388 : Nat := 2098794665419559309352451

theorem tailTrace_4087388 : CollatzResearch.WordTrace tailWord_4087388 prefixEnd_4087388 2098794665419559309352451 := by
  unfold tailWord_4087388
  simp only [CollatzResearch.WordTrace]
  refine ⟨74539643858049410569647409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99386191810732547426196545 74539643858049410569647409)
  ·
    refine ⟨55904732893537057927235557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74539643858049410569647409 55904732893537057927235557)
    ·
      refine ⟨10482137417538198361356667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55904732893537057927235557 10482137417538198361356667)
      ·
        refine ⟨15723206126307297542035001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10482137417538198361356667 15723206126307297542035001)
        ·
          refine ⟨11792404594730473156526251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15723206126307297542035001 11792404594730473156526251)
          ·
            refine ⟨17688606892095709734789377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11792404594730473156526251 17688606892095709734789377)
            ·
              refine ⟨13266455169071782301092033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17688606892095709734789377 13266455169071782301092033)
              ·
                refine ⟨9949841376803836725819025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13266455169071782301092033 9949841376803836725819025)
                ·
                  refine ⟨7462381032602877544364269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9949841376803836725819025 7462381032602877544364269)
                  ·
                    refine ⟨2798392887226079079136601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7462381032602877544364269 2798392887226079079136601)
                    ·
                      refine ⟨2098794665419559309352451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2798392887226079079136601 2098794665419559309352451)
                      ·
                        rfl

theorem cell23_4087388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_4087388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087388 prefixEnd_4087388 := by exact prefixLift 4087388
  have htrace : WordTrace (prefixWord ++ tailWord_4087388) baseStart_4087388 baseEnd_4087388 := by
    simpa [prefixWord, tailWord_4087388, baseEnd_4087388] using wordTrace_append hprefix tailTrace_4087388
  have hstable : (prefixWord ++ tailWord_4087388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087388).length < 2 ^ (prefixWord ++ tailWord_4087388).sum := by decide
  have hdescent : baseEnd_4087388 < baseStart_4087388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087389 : List Nat := [1, 4, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_4087389 : Nat := 118140960795 + 4087389 * 2 ^ 59
def prefixEnd_4087389 : Nat := 4983230072969 + 3 ^ 40 * 4087389 * 2
def baseEnd_4087389 : Nat := 699598392966737935146649

theorem tailTrace_4087389 : CollatzResearch.WordTrace tailWord_4087389 prefixEnd_4087389 699598392966737935146649 := by
  unfold tailWord_4087389
  simp only [CollatzResearch.WordTrace]
  refine ⟨149079324189095198310081221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99386216126063465540054147 149079324189095198310081221)
  ·
    refine ⟨27952373285455349683140229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149079324189095198310081221 27952373285455349683140229)
    ·
      refine ⟨5241069991022878065588793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27952373285455349683140229 5241069991022878065588793)
      ·
        refine ⟨3930802493267158549191595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5241069991022878065588793 3930802493267158549191595)
        ·
          refine ⟨5896203739900737823787393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930802493267158549191595 5896203739900737823787393)
          ·
            refine ⟨4422152804925553367840545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5896203739900737823787393 4422152804925553367840545)
            ·
              refine ⟨3316614603694165025880409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4422152804925553367840545 3316614603694165025880409)
              ·
                refine ⟨2487460952770623769410307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3316614603694165025880409 2487460952770623769410307)
                ·
                  refine ⟨3731191429155935654115461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487460952770623769410307 3731191429155935654115461)
                  ·
                    refine ⟨699598392966737935146649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3731191429155935654115461 699598392966737935146649)
                    ·
                      rfl

theorem cell23_4087389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_4087389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087389 prefixEnd_4087389 := by exact prefixLift 4087389
  have htrace : WordTrace (prefixWord ++ tailWord_4087389) baseStart_4087389 baseEnd_4087389 := by
    simpa [prefixWord, tailWord_4087389, baseEnd_4087389] using wordTrace_append hprefix tailTrace_4087389
  have hstable : (prefixWord ++ tailWord_4087389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087389).length < 2 ^ (prefixWord ++ tailWord_4087389).sum := by decide
  have hdescent : baseEnd_4087389 < baseStart_4087389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087395 : List Nat := [1, 1, 1, 5, 1, 3, 4, 2, 1, 1, 3]
def baseStart_4087395 : Nat := 118140960795 + 4087395 * 2 ^ 59
def prefixEnd_4087395 : Nat := 4983230072969 + 3 ^ 40 * 4087395 * 2
def baseEnd_4087395 : Nat := 2098798259784140781964919

theorem tailTrace_4087395 : CollatzResearch.WordTrace tailWord_4087395 prefixEnd_4087395 2098798259784140781964919 := by
  unfold tailWord_4087395
  simp only [CollatzResearch.WordTrace]
  refine ⟨149079543027073461334799639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99386362018048974223199759 149079543027073461334799639)
  ·
    refine ⟨223619314540610192002199459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149079543027073461334799639 223619314540610192002199459)
    ·
      refine ⟨335428971810915288003299189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223619314540610192002199459 335428971810915288003299189)
      ·
        refine ⟨31446466107273308250309299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335428971810915288003299189 31446466107273308250309299)
        ·
          refine ⟨47169699160909962375463949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31446466107273308250309299 47169699160909962375463949)
          ·
            refine ⟨17688637185341235890798981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47169699160909962375463949 17688637185341235890798981)
            ·
              refine ⟨3316619472251481729524809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17688637185341235890798981 3316619472251481729524809)
              ·
                refine ⟨2487464604188611297143607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3316619472251481729524809 2487464604188611297143607)
                ·
                  refine ⟨3731196906282916945715411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487464604188611297143607 3731196906282916945715411)
                  ·
                    refine ⟨5596795359424375418573117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3731196906282916945715411 5596795359424375418573117)
                    ·
                      refine ⟨2098798259784140781964919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5596795359424375418573117 2098798259784140781964919)
                      ·
                        rfl

theorem cell23_4087395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_4087395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087395 prefixEnd_4087395 := by exact prefixLift 4087395
  have htrace : WordTrace (prefixWord ++ tailWord_4087395) baseStart_4087395 baseEnd_4087395 := by
    simpa [prefixWord, tailWord_4087395, baseEnd_4087395] using wordTrace_append hprefix tailTrace_4087395
  have hstable : (prefixWord ++ tailWord_4087395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087395).length < 2 ^ (prefixWord ++ tailWord_4087395).sum := by decide
  have hdescent : baseEnd_4087395 < baseStart_4087395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087421 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_4087421 : Nat := 118140960795 + 4087421 * 2 ^ 59
def prefixEnd_4087421 : Nat := 4983230072969 + 3 ^ 40 * 4087421 * 2
def baseEnd_4087421 : Nat := 2098811610281157680239799

theorem tailTrace_4087421 : CollatzResearch.WordTrace tailWord_4087421 prefixEnd_4087421 2098811610281157680239799 := by
  unfold tailWord_4087421
  simp only [CollatzResearch.WordTrace]
  refine ⟨149080491324979267775246117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99386994216652845183497411 149080491324979267775246117)
  ·
    refine ⟨27952592123433612707858647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149080491324979267775246117 27952592123433612707858647)
    ·
      refine ⟨41928888185150419061787971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27952592123433612707858647 41928888185150419061787971)
      ·
        refine ⟨62893332277725628592681957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41928888185150419061787971 62893332277725628592681957)
        ·
          refine ⟨11792499802073555361127867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62893332277725628592681957 11792499802073555361127867)
          ·
            refine ⟨17688749703110333041691801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11792499802073555361127867 17688749703110333041691801)
            ·
              refine ⟨13266562277332749781268851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17688749703110333041691801 13266562277332749781268851)
              ·
                refine ⟨19899843415999124671903277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13266562277332749781268851 19899843415999124671903277)
                ·
                  refine ⟨7462441280999671751963729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19899843415999124671903277 7462441280999671751963729)
                  ·
                    refine ⟨5596830960749753813972797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7462441280999671751963729 5596830960749753813972797)
                    ·
                      refine ⟨2098811610281157680239799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5596830960749753813972797 2098811610281157680239799)
                      ·
                        rfl

theorem cell23_4087421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_4087421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087421 prefixEnd_4087421 := by exact prefixLift 4087421
  have htrace : WordTrace (prefixWord ++ tailWord_4087421) baseStart_4087421 baseEnd_4087421 := by
    simpa [prefixWord, tailWord_4087421, baseEnd_4087421] using wordTrace_append hprefix tailTrace_4087421
  have hstable : (prefixWord ++ tailWord_4087421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087421).length < 2 ^ (prefixWord ++ tailWord_4087421).sum := by decide
  have hdescent : baseEnd_4087421 < baseStart_4087421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087424 : List Nat := [2, 1, 1, 2, 1, 4, 5, 7]
def baseStart_4087424 : Nat := 118140960795 + 4087424 * 2 ^ 59
def prefixEnd_4087424 : Nat := 4983230072969 + 3 ^ 40 * 4087424 * 2
def baseEnd_4087424 : Nat := 77733820397152635870455

theorem tailTrace_4087424 : CollatzResearch.WordTrace tailWord_4087424 prefixEnd_4087424 77733820397152635870455 := by
  unfold tailWord_4087424
  simp only [CollatzResearch.WordTrace]
  refine ⟨74540300371984199643802663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99387067162645599525070217 74540300371984199643802663)
  ·
    refine ⟨111810450557976299465703995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74540300371984199643802663 111810450557976299465703995)
    ·
      refine ⟨167715675836964449198555993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111810450557976299465703995 167715675836964449198555993)
      ·
        refine ⟨125786756877723336898916995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167715675836964449198555993 125786756877723336898916995)
        ·
          refine ⟨188680135316585005348375493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125786756877723336898916995 188680135316585005348375493)
          ·
            refine ⟨35377525371859688502820405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188680135316585005348375493 35377525371859688502820405)
            ·
              refine ⟨3316643003611845797139413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35377525371859688502820405 3316643003611845797139413)
              ·
                refine ⟨77733820397152635870455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3316643003611845797139413 77733820397152635870455)
                ·
                  rfl

theorem cell23_4087424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 7].length) (baseStart_4087424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087424 prefixEnd_4087424 := by exact prefixLift 4087424
  have htrace : WordTrace (prefixWord ++ tailWord_4087424) baseStart_4087424 baseEnd_4087424 := by
    simpa [prefixWord, tailWord_4087424, baseEnd_4087424] using wordTrace_append hprefix tailTrace_4087424
  have hstable : (prefixWord ++ tailWord_4087424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087424).length < 2 ^ (prefixWord ++ tailWord_4087424).sum := by decide
  have hdescent : baseEnd_4087424 < baseStart_4087424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087432 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 1, 5]
def baseStart_4087432 : Nat := 118140960795 + 4087432 * 2 ^ 59
def prefixEnd_4087432 : Nat := 4983230072969 + 3 ^ 40 * 4087432 * 2
def baseEnd_4087432 : Nat := 699605752856119045734083

theorem tailTrace_4087432 : CollatzResearch.WordTrace tailWord_4087432 prefixEnd_4087432 699605752856119045734083 := by
  unfold tailWord_4087432
  simp only [CollatzResearch.WordTrace]
  refine ⟨74540446263969708326948275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99387261685292944435931033 74540446263969708326948275)
  ·
    refine ⟨111810669395954562490422413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74540446263969708326948275 111810669395954562490422413)
    ·
      refine ⟨41929001023482960933908405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111810669395954562490422413 41929001023482960933908405)
      ·
        refine ⟨3930843845951527587553913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41929001023482960933908405 3930843845951527587553913)
        ·
          refine ⟨2948132884463645690665435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3930843845951527587553913 2948132884463645690665435)
          ·
            refine ⟨4422199326695468535998153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948132884463645690665435 4422199326695468535998153)
            ·
              refine ⟨3316649495021601401998615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4422199326695468535998153 3316649495021601401998615)
              ·
                refine ⟨4974974242532402102997923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316649495021601401998615 4974974242532402102997923)
                ·
                  refine ⟨7462461363798603154496885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974974242532402102997923 7462461363798603154496885)
                  ·
                    refine ⟨699605752856119045734083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7462461363798603154496885 699605752856119045734083)
                    ·
                      rfl

theorem cell23_4087432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_4087432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087432 prefixEnd_4087432 := by exact prefixLift 4087432
  have htrace : WordTrace (prefixWord ++ tailWord_4087432) baseStart_4087432 baseEnd_4087432 := by
    simpa [prefixWord, tailWord_4087432, baseEnd_4087432] using wordTrace_append hprefix tailTrace_4087432
  have hstable : (prefixWord ++ tailWord_4087432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087432).length < 2 ^ (prefixWord ++ tailWord_4087432).sum := by decide
  have hdescent : baseEnd_4087432 < baseStart_4087432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087435 : List Nat := [1, 1, 1, 1, 4, 1, 6, 3, 1, 2, 2]
def baseStart_4087435 : Nat := 118140960795 + 4087435 * 2 ^ 59
def prefixEnd_4087435 : Nat := 4983230072969 + 3 ^ 40 * 4087435 * 2
def baseEnd_4087435 : Nat := 2098818799010320625464735

theorem tailTrace_4087435 : CollatzResearch.WordTrace tailWord_4087435 prefixEnd_4087435 2098818799010320625464735 := by
  unfold tailWord_4087435
  simp only [CollatzResearch.WordTrace]
  refine ⟨149081001946928548166255759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99387334631285698777503839 149081001946928548166255759)
  ·
    refine ⟨223621502920392822249383639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149081001946928548166255759 223621502920392822249383639)
    ·
      refine ⟨335432254380589233374075459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223621502920392822249383639 335432254380589233374075459)
      ·
        refine ⟨503148381570883850061113189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335432254380589233374075459 503148381570883850061113189)
        ·
          refine ⟨94340321544540721886458723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503148381570883850061113189 94340321544540721886458723)
          ·
            refine ⟨141510482316811082829688085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94340321544540721886458723 141510482316811082829688085)
            ·
              refine ⟨6633303858600519507641629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141510482316811082829688085 6633303858600519507641629)
              ·
                refine ⟨2487488946975194815365611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6633303858600519507641629 2487488946975194815365611)
                ·
                  refine ⟨3731233420462792223048417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487488946975194815365611 3731233420462792223048417)
                  ·
                    refine ⟨2798425065347094167286313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3731233420462792223048417 2798425065347094167286313)
                    ·
                      refine ⟨2098818799010320625464735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2798425065347094167286313 2098818799010320625464735)
                      ·
                        rfl

theorem cell23_4087435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 1, 2, 2].length) (baseStart_4087435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087435 prefixEnd_4087435 := by exact prefixLift 4087435
  have htrace : WordTrace (prefixWord ++ tailWord_4087435) baseStart_4087435 baseEnd_4087435 := by
    simpa [prefixWord, tailWord_4087435, baseEnd_4087435] using wordTrace_append hprefix tailTrace_4087435
  have hstable : (prefixWord ++ tailWord_4087435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087435).length < 2 ^ (prefixWord ++ tailWord_4087435).sum := by decide
  have hdescent : baseEnd_4087435 < baseStart_4087435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087438 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_4087438 : Nat := 118140960795 + 4087438 * 2 ^ 59
def prefixEnd_4087438 : Nat := 4983230072969 + 3 ^ 40 * 4087438 * 2
def baseEnd_4087438 : Nat := 2098820339452284113727221

theorem tailTrace_4087438 : CollatzResearch.WordTrace tailWord_4087438 prefixEnd_4087438 2098820339452284113727221 := by
  unfold tailWord_4087438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18635138920739709959826871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99387407577278453119076645 18635138920739709959826871)
  ·
    refine ⟨27952708381109564939740307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18635138920739709959826871 27952708381109564939740307)
    ·
      refine ⟨41929062571664347409610461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27952708381109564939740307 41929062571664347409610461)
      ·
        refine ⟨15723398464374130278603923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41929062571664347409610461 15723398464374130278603923)
        ·
          refine ⟨23585097696561195417905885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15723398464374130278603923 23585097696561195417905885)
          ·
            refine ⟨8844411636210448281714707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23585097696561195417905885 8844411636210448281714707)
            ·
              refine ⟨13266617454315672422572061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8844411636210448281714707 13266617454315672422572061)
              ·
                refine ⟨4974981545368377158464523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13266617454315672422572061 4974981545368377158464523)
                ·
                  refine ⟨7462472318052565737696785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974981545368377158464523 7462472318052565737696785)
                  ·
                    refine ⟨5596854238539424303272589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7462472318052565737696785 5596854238539424303272589)
                    ·
                      refine ⟨2098820339452284113727221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5596854238539424303272589 2098820339452284113727221)
                      ·
                        rfl

theorem cell23_4087438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_4087438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087438 prefixEnd_4087438 := by exact prefixLift 4087438
  have htrace : WordTrace (prefixWord ++ tailWord_4087438) baseStart_4087438 baseEnd_4087438 := by
    simpa [prefixWord, tailWord_4087438, baseEnd_4087438] using wordTrace_append hprefix tailTrace_4087438
  have hstable : (prefixWord ++ tailWord_4087438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087438).length < 2 ^ (prefixWord ++ tailWord_4087438).sum := by decide
  have hdescent : baseEnd_4087438 < baseStart_4087438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087461 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 5, 3, 2]
def baseStart_4087461 : Nat := 118140960795 + 4087461 * 2 ^ 59
def prefixEnd_4087461 : Nat := 4983230072969 + 3 ^ 40 * 4087461 * 2
def baseEnd_4087461 : Nat := 2098832149507337523739615

theorem tailTrace_4087461 : CollatzResearch.WordTrace tailWord_4087461 prefixEnd_4087461 2098832149507337523739615 := by
  unfold tailWord_4087461
  simp only [CollatzResearch.WordTrace]
  refine ⟨149081950244834354606702237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99387966829889569737801491 149081950244834354606702237)
  ·
    refine ⟨55905731341812882977513339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149081950244834354606702237 55905731341812882977513339)
    ·
      refine ⟨83858597012719324466270009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55905731341812882977513339 83858597012719324466270009)
      ·
        refine ⟨62893947759539493349702507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83858597012719324466270009 62893947759539493349702507)
        ·
          refine ⟨94340921639309240024553761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62893947759539493349702507 94340921639309240024553761)
          ·
            refine ⟨70755691229481930018415321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94340921639309240024553761 70755691229481930018415321)
            ·
              refine ⟨53066768422111447513811491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70755691229481930018415321 53066768422111447513811491)
              ·
                refine ⟨79600152633167171270717237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53066768422111447513811491 79600152633167171270717237)
                ·
                  refine ⟨7462514309359422306629741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79600152633167171270717237 7462514309359422306629741)
                  ·
                    refine ⟨2798442866009783364986153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7462514309359422306629741 2798442866009783364986153)
                    ·
                      refine ⟨2098832149507337523739615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2798442866009783364986153 2098832149507337523739615)
                      ·
                        rfl

theorem cell23_4087461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_4087461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087461 prefixEnd_4087461 := by exact prefixLift 4087461
  have htrace : WordTrace (prefixWord ++ tailWord_4087461) baseStart_4087461 baseEnd_4087461 := by
    simpa [prefixWord, tailWord_4087461, baseEnd_4087461] using wordTrace_append hprefix tailTrace_4087461
  have hstable : (prefixWord ++ tailWord_4087461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087461).length < 2 ^ (prefixWord ++ tailWord_4087461).sum := by decide
  have hdescent : baseEnd_4087461 < baseStart_4087461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087474 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_4087474 : Nat := 118140960795 + 4087474 * 2 ^ 59
def prefixEnd_4087474 : Nat := 4983230072969 + 3 ^ 40 * 4087474 * 2
def baseEnd_4087474 : Nat := 2098838824755845972877055

theorem tailTrace_4087474 : CollatzResearch.WordTrace tailWord_4087474 prefixEnd_4087474 2098838824755845972877055 := by
  unfold tailWord_4087474
  simp only [CollatzResearch.WordTrace]
  refine ⟨37270606098446814456731369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99388282929191505217950317 37270606098446814456731369)
  ·
    refine ⟨27952954573835110842548527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37270606098446814456731369 27952954573835110842548527)
    ·
      refine ⟨41929431860752666263822791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27952954573835110842548527 41929431860752666263822791)
      ·
        refine ⟨62894147791128999395734187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41929431860752666263822791 62894147791128999395734187)
        ·
          refine ⟨94341221686693499093601281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62894147791128999395734187 94341221686693499093601281)
          ·
            refine ⟨70755916265020124320200961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94341221686693499093601281 70755916265020124320200961)
            ·
              refine ⟨53066937198765093240150721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70755916265020124320200961 53066937198765093240150721)
              ·
                refine ⟨39800202899073819930113041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53066937198765093240150721 39800202899073819930113041)
                ·
                  refine ⟨29850152174305364947584781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39800202899073819930113041 29850152174305364947584781)
                  ·
                    refine ⟨11193807065364511855344293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29850152174305364947584781 11193807065364511855344293)
                    ·
                      refine ⟨2098838824755845972877055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11193807065364511855344293 2098838824755845972877055)
                      ·
                        rfl

theorem cell23_4087474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_4087474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087474 prefixEnd_4087474 := by exact prefixLift 4087474
  have htrace : WordTrace (prefixWord ++ tailWord_4087474) baseStart_4087474 baseEnd_4087474 := by
    simpa [prefixWord, tailWord_4087474, baseEnd_4087474] using wordTrace_append hprefix tailTrace_4087474
  have hstable : (prefixWord ++ tailWord_4087474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087474).length < 2 ^ (prefixWord ++ tailWord_4087474).sum := by decide
  have hdescent : baseEnd_4087474 < baseStart_4087474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087504 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 4]
def baseStart_4087504 : Nat := 118140960795 + 4087504 * 2 ^ 59
def prefixEnd_4087504 : Nat := 4983230072969 + 3 ^ 40 * 4087504 * 2
def baseEnd_4087504 : Nat := 2098854229175480855501917

theorem tailTrace_4087504 : CollatzResearch.WordTrace tailWord_4087504 prefixEnd_4087504 2098854229175480855501917 := by
  unfold tailWord_4087504
  simp only [CollatzResearch.WordTrace]
  refine ⟨74541759291839286475258783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99389012389119048633678377 74541759291839286475258783)
  ·
    refine ⟨111812638937758929712888175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74541759291839286475258783 111812638937758929712888175)
    ·
      refine ⟨167718958406638394569332263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111812638937758929712888175 167718958406638394569332263)
      ·
        refine ⟨251578437609957591853998395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167718958406638394569332263 251578437609957591853998395)
        ·
          refine ⟨377367656414936387780997593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251578437609957591853998395 377367656414936387780997593)
          ·
            refine ⟨283025742311202290835748195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377367656414936387780997593 283025742311202290835748195)
            ·
              refine ⟨424538613466803436253622293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283025742311202290835748195 424538613466803436253622293)
              ·
                refine ⟨19900247506256411074388545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 424538613466803436253622293 19900247506256411074388545)
                ·
                  refine ⟨14925185629692308305791409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19900247506256411074388545 14925185629692308305791409)
                  ·
                    refine ⟨11193889222269231229343557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14925185629692308305791409 11193889222269231229343557)
                    ·
                      refine ⟨2098854229175480855501917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11193889222269231229343557 2098854229175480855501917)
                      ·
                        rfl

theorem cell23_4087504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_4087504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087504 prefixEnd_4087504 := by exact prefixLift 4087504
  have htrace : WordTrace (prefixWord ++ tailWord_4087504) baseStart_4087504 baseEnd_4087504 := by
    simpa [prefixWord, tailWord_4087504, baseEnd_4087504] using wordTrace_append hprefix tailTrace_4087504
  have hstable : (prefixWord ++ tailWord_4087504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087504).length < 2 ^ (prefixWord ++ tailWord_4087504).sum := by decide
  have hdescent : baseEnd_4087504 < baseStart_4087504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087525 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 2, 2, 2]
def baseStart_4087525 : Nat := 118140960795 + 4087525 * 2 ^ 59
def prefixEnd_4087525 : Nat := 4983230072969 + 3 ^ 40 * 4087525 * 2
def baseEnd_4087525 : Nat := 2098865012269225273339321

theorem tailTrace_4087525 : CollatzResearch.WordTrace tailWord_4087525 prefixEnd_4087525 2098865012269225273339321 := by
  unfold tailWord_4087525
  simp only [CollatzResearch.WordTrace]
  refine ⟨149084284516602493537032029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99389523011068329024688019 149084284516602493537032029)
  ·
    refine ⟨55906606693725935076387011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149084284516602493537032029 55906606693725935076387011)
    ·
      refine ⟨83859910040588902614580517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55906606693725935076387011 83859910040588902614580517)
      ·
        refine ⟨15723733132610419240233847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83859910040588902614580517 15723733132610419240233847)
        ·
          refine ⟨23585599698915628860350771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15723733132610419240233847 23585599698915628860350771)
          ·
            refine ⟨35378399548373443290526157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23585599698915628860350771 35378399548373443290526157)
            ·
              refine ⟨13266899830640041233947309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35378399548373443290526157 13266899830640041233947309)
              ·
                refine ⟨4975087436490015462730241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13266899830640041233947309 4975087436490015462730241)
                ·
                  refine ⟨3731315577367511597047681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4975087436490015462730241 3731315577367511597047681)
                  ·
                    refine ⟨2798486683025633697785761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3731315577367511597047681 2798486683025633697785761)
                    ·
                      refine ⟨2098865012269225273339321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2798486683025633697785761 2098865012269225273339321)
                      ·
                        rfl

theorem cell23_4087525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_4087525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087525 prefixEnd_4087525 := by exact prefixLift 4087525
  have htrace : WordTrace (prefixWord ++ tailWord_4087525) baseStart_4087525 baseEnd_4087525 := by
    simpa [prefixWord, tailWord_4087525, baseEnd_4087525] using wordTrace_append hprefix tailTrace_4087525
  have hstable : (prefixWord ++ tailWord_4087525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087525).length < 2 ^ (prefixWord ++ tailWord_4087525).sum := by decide
  have hdescent : baseEnd_4087525 < baseStart_4087525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087572 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_4087572 : Nat := 118140960795 + 4087572 * 2 ^ 59
def prefixEnd_4087572 : Nat := 4983230072969 + 3 ^ 40 * 4087572 * 2
def baseEnd_4087572 : Nat := 2098889145859986589451605

theorem tailTrace_4087572 : CollatzResearch.WordTrace tailWord_4087572 prefixEnd_4087572 2098889145859986589451605 := by
  unfold tailWord_4087572
  simp only [CollatzResearch.WordTrace]
  refine ⟨74542999373716110281996485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99390665831621480375995313 74542999373716110281996485)
  ·
    refine ⟨13976812382571770677874341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74542999373716110281996485 13976812382571770677874341)
    ·
      refine ⟨2620652321732207002101439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13976812382571770677874341 2620652321732207002101439)
      ·
        refine ⟨3930978482598310503152159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2620652321732207002101439 3930978482598310503152159)
        ·
          refine ⟨5896467723897465754728239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930978482598310503152159 5896467723897465754728239)
          ·
            refine ⟨8844701585846198632092359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896467723897465754728239 8844701585846198632092359)
            ·
              refine ⟨13267052378769297948138539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8844701585846198632092359 13267052378769297948138539)
              ·
                refine ⟨19900578568153946922207809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13267052378769297948138539 19900578568153946922207809)
                ·
                  refine ⟨14925433926115460191655857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19900578568153946922207809 14925433926115460191655857)
                  ·
                    refine ⟨11194075444586595143741893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14925433926115460191655857 11194075444586595143741893)
                    ·
                      refine ⟨2098889145859986589451605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11194075444586595143741893 2098889145859986589451605)
                      ·
                        rfl

theorem cell23_4087572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_4087572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087572 prefixEnd_4087572 := by exact prefixLift 4087572
  have htrace : WordTrace (prefixWord ++ tailWord_4087572) baseStart_4087572 baseEnd_4087572 := by
    simpa [prefixWord, tailWord_4087572, baseEnd_4087572] using wordTrace_append hprefix tailTrace_4087572
  have hstable : (prefixWord ++ tailWord_4087572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087572).length < 2 ^ (prefixWord ++ tailWord_4087572).sum := by decide
  have hdescent : baseEnd_4087572 < baseStart_4087572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087671 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_4087671 : Nat := 118140960795 + 4087671 * 2 ^ 59
def prefixEnd_4087671 : Nat := 4983230072969 + 3 ^ 40 * 4087671 * 2
def baseEnd_4087671 : Nat := 2098939980444781702113649

theorem tailTrace_4087671 : CollatzResearch.WordTrace tailWord_4087671 prefixEnd_4087671 2098939980444781702113649 := by
  unfold tailWord_4087671
  simp only [CollatzResearch.WordTrace]
  refine ⟨149089609574073560471846867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99393073049382373647897911 149089609574073560471846867)
  ·
    refine ⟨223634414361110340707770301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149089609574073560471846867 223634414361110340707770301)
    ·
      refine ⟨83862905385416377765413863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223634414361110340707770301 83862905385416377765413863)
      ·
        refine ⟨125794358078124566648120795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83862905385416377765413863 125794358078124566648120795)
        ·
          refine ⟨188691537117186849972181193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125794358078124566648120795 188691537117186849972181193)
          ·
            refine ⟨141518652837890137479135895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188691537117186849972181193 141518652837890137479135895)
            ·
              refine ⟨212277979256835206218703843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141518652837890137479135895 212277979256835206218703843)
              ·
                refine ⟨318416968885252809328055765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212277979256835206218703843 318416968885252809328055765)
                ·
                  refine ⟨7462897708248112718626307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 318416968885252809328055765 7462897708248112718626307)
                  ·
                    refine ⟨11194346562372169077939461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7462897708248112718626307 11194346562372169077939461)
                    ·
                      refine ⟨2098939980444781702113649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11194346562372169077939461 2098939980444781702113649)
                      ·
                        rfl

theorem cell23_4087671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_4087671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087671 prefixEnd_4087671 := by exact prefixLift 4087671
  have htrace : WordTrace (prefixWord ++ tailWord_4087671) baseStart_4087671 baseEnd_4087671 := by
    simpa [prefixWord, tailWord_4087671, baseEnd_4087671] using wordTrace_append hprefix tailTrace_4087671
  have hstable : (prefixWord ++ tailWord_4087671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087671).length < 2 ^ (prefixWord ++ tailWord_4087671).sum := by decide
  have hdescent : baseEnd_4087671 < baseStart_4087671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087691 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 3]
def baseStart_4087691 : Nat := 118140960795 + 4087691 * 2 ^ 59
def prefixEnd_4087691 : Nat := 4983230072969 + 3 ^ 40 * 4087691 * 2
def baseEnd_4087691 : Nat := 2098950250057871623863557

theorem tailTrace_4087691 : CollatzResearch.WordTrace tailWord_4087691 prefixEnd_4087691 2098950250057871623863557 := by
  unfold tailWord_4087691
  simp only [CollatzResearch.WordTrace]
  refine ⟨149090339034001103887574927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99393559356000735925049951 149090339034001103887574927)
  ·
    refine ⟨223635508551001655831362391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149090339034001103887574927 223635508551001655831362391)
    ·
      refine ⟨335453262826502483747043587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223635508551001655831362391 335453262826502483747043587)
      ·
        refine ⟨503179894239753725620565381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335453262826502483747043587 503179894239753725620565381)
        ·
          refine ⟨94346230169953823553856009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503179894239753725620565381 94346230169953823553856009)
          ·
            refine ⟨70759672627465367665392007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94346230169953823553856009 70759672627465367665392007)
            ·
              refine ⟨106139508941198051498088011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70759672627465367665392007 106139508941198051498088011)
              ·
                refine ⟨159209263411797077247132017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106139508941198051498088011 159209263411797077247132017)
                ·
                  refine ⟨119406947558847807935349013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159209263411797077247132017 119406947558847807935349013)
                  ·
                    refine ⟨5597200666820990996969485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119406947558847807935349013 5597200666820990996969485)
                    ·
                      refine ⟨2098950250057871623863557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5597200666820990996969485 2098950250057871623863557)
                      ·
                        rfl

theorem cell23_4087691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 3].length) (baseStart_4087691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087691 prefixEnd_4087691 := by exact prefixLift 4087691
  have htrace : WordTrace (prefixWord ++ tailWord_4087691) baseStart_4087691 baseEnd_4087691 := by
    simpa [prefixWord, tailWord_4087691, baseEnd_4087691] using wordTrace_append hprefix tailTrace_4087691
  have hstable : (prefixWord ++ tailWord_4087691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087691).length < 2 ^ (prefixWord ++ tailWord_4087691).sum := by decide
  have hdescent : baseEnd_4087691 < baseStart_4087691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087701 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_4087701 : Nat := 118140960795 + 4087701 * 2 ^ 59
def prefixEnd_4087701 : Nat := 4983230072969 + 3 ^ 40 * 4087701 * 2
def baseEnd_4087701 : Nat := 2098955384864416584738511

theorem tailTrace_4087701 : CollatzResearch.WordTrace tailWord_4087701 prefixEnd_4087701 2098955384864416584738511 := by
  unfold tailWord_4087701
  simp only [CollatzResearch.WordTrace]
  refine ⟨149090703763964875595438957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99393802509309917063625971 149090703763964875595438957)
  ·
    refine ⟨55909013911486828348289609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149090703763964875595438957 55909013911486828348289609)
    ·
      refine ⟨41931760433615121261217207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55909013911486828348289609 41931760433615121261217207)
      ·
        refine ⟨62897640650422681891825811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41931760433615121261217207 62897640650422681891825811)
        ·
          refine ⟨94346460975634022837738717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62897640650422681891825811 94346460975634022837738717)
          ·
            refine ⟨35379922865862758564152019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94346460975634022837738717 35379922865862758564152019)
            ·
              refine ⟨53069884298794137846228029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35379922865862758564152019 53069884298794137846228029)
              ·
                refine ⟨19901206612047801692335511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53069884298794137846228029 19901206612047801692335511)
                ·
                  refine ⟨29851809918071702538503267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19901206612047801692335511 29851809918071702538503267)
                  ·
                    refine ⟨44777714877107553807754901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29851809918071702538503267 44777714877107553807754901)
                    ·
                      refine ⟨2098955384864416584738511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44777714877107553807754901 2098955384864416584738511)
                      ·
                        rfl

theorem cell23_4087701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_4087701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087701 prefixEnd_4087701 := by exact prefixLift 4087701
  have htrace : WordTrace (prefixWord ++ tailWord_4087701) baseStart_4087701 baseEnd_4087701 := by
    simpa [prefixWord, tailWord_4087701, baseEnd_4087701] using wordTrace_append hprefix tailTrace_4087701
  have hstable : (prefixWord ++ tailWord_4087701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087701).length < 2 ^ (prefixWord ++ tailWord_4087701).sum := by decide
  have hdescent : baseEnd_4087701 < baseStart_4087701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087705 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 3, 2, 2]
def baseStart_4087705 : Nat := 118140960795 + 4087705 * 2 ^ 59
def prefixEnd_4087705 : Nat := 4983230072969 + 3 ^ 40 * 4087705 * 2
def baseEnd_4087705 : Nat := 2098957438787034569088493

theorem tailTrace_4087705 : CollatzResearch.WordTrace tailWord_4087705 prefixEnd_4087705 2098957438787034569088493 := by
  unfold tailWord_4087705
  simp only [CollatzResearch.WordTrace]
  refine ⟨149090849655950384278584569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99393899770633589519056379 149090849655950384278584569)
  ·
    refine ⟨111818137241962788208938427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149090849655950384278584569 111818137241962788208938427)
    ·
      refine ⟨167727205862944182313407641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111818137241962788208938427 167727205862944182313407641)
      ·
        refine ⟨125795404397208136735055731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167727205862944182313407641 125795404397208136735055731)
        ·
          refine ⟨188693106595812205102583597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125795404397208136735055731 188693106595812205102583597)
          ·
            refine ⟨70759914973429576913468849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188693106595812205102583597 70759914973429576913468849)
            ·
              refine ⟨53069936230072182685101637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70759914973429576913468849 53069936230072182685101637)
              ·
                refine ⟨9950613043138534253456557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53069936230072182685101637 9950613043138534253456557)
                ·
                  refine ⟨3731479891176950345046209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9950613043138534253456557 3731479891176950345046209)
                  ·
                    refine ⟨2798609918382712758784657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3731479891176950345046209 2798609918382712758784657)
                    ·
                      refine ⟨2098957438787034569088493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2798609918382712758784657 2098957438787034569088493)
                      ·
                        rfl

theorem cell23_4087705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 2, 2].length) (baseStart_4087705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087705 prefixEnd_4087705 := by exact prefixLift 4087705
  have htrace : WordTrace (prefixWord ++ tailWord_4087705) baseStart_4087705 baseEnd_4087705 := by
    simpa [prefixWord, tailWord_4087705, baseEnd_4087705] using wordTrace_append hprefix tailTrace_4087705
  have hstable : (prefixWord ++ tailWord_4087705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087705).length < 2 ^ (prefixWord ++ tailWord_4087705).sum := by decide
  have hdescent : baseEnd_4087705 < baseStart_4087705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087751 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_4087751 : Nat := 118140960795 + 4087751 * 2 ^ 59
def prefixEnd_4087751 : Nat := 4983230072969 + 3 ^ 40 * 4087751 * 2
def baseEnd_4087751 : Nat := 2098981058897141389113281

theorem tailTrace_4087751 : CollatzResearch.WordTrace tailWord_4087751 prefixEnd_4087751 2098981058897141389113281 := by
  unfold tailWord_4087751
  simp only [CollatzResearch.WordTrace]
  refine ⟨149092527413783734134759107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99395018275855822756506071 149092527413783734134759107)
  ·
    refine ⟨223638791120675601202138661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149092527413783734134759107 223638791120675601202138661)
    ·
      refine ⟨41932273335126675225400999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223638791120675601202138661 41932273335126675225400999)
      ·
        refine ⟨62898410002690012838101499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41932273335126675225400999 62898410002690012838101499)
        ·
          refine ⟨94347615004035019257152249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62898410002690012838101499 94347615004035019257152249)
          ·
            refine ⟨70760711253026264442864187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94347615004035019257152249 70760711253026264442864187)
            ·
              refine ⟨106141066879539396664296281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70760711253026264442864187 106141066879539396664296281)
              ·
                refine ⟨79605800159654547498222211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106141066879539396664296281 79605800159654547498222211)
                ·
                  refine ⟨119408700239481821247333317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79605800159654547498222211 119408700239481821247333317)
                  ·
                    refine ⟨22389131294902841483874997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119408700239481821247333317 22389131294902841483874997)
                    ·
                      refine ⟨2098981058897141389113281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22389131294902841483874997 2098981058897141389113281)
                      ·
                        rfl

theorem cell23_4087751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_4087751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087751 prefixEnd_4087751 := by exact prefixLift 4087751
  have htrace : WordTrace (prefixWord ++ tailWord_4087751) baseStart_4087751 baseEnd_4087751 := by
    simpa [prefixWord, tailWord_4087751, baseEnd_4087751] using wordTrace_append hprefix tailTrace_4087751
  have hstable : (prefixWord ++ tailWord_4087751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087751).length < 2 ^ (prefixWord ++ tailWord_4087751).sum := by decide
  have hdescent : baseEnd_4087751 < baseStart_4087751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087755 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 2, 1, 3]
def baseStart_4087755 : Nat := 118140960795 + 4087755 * 2 ^ 59
def prefixEnd_4087755 : Nat := 4983230072969 + 3 ^ 40 * 4087755 * 2
def baseEnd_4087755 : Nat := 2098983112819759373463263

theorem tailTrace_4087755 : CollatzResearch.WordTrace tailWord_4087755 prefixEnd_4087755 2098983112819759373463263 := by
  unfold tailWord_4087755
  simp only [CollatzResearch.WordTrace]
  refine ⟨149092673305769242817904719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99395115537179495211936479 149092673305769242817904719)
  ·
    refine ⟨223639009958653864226857079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149092673305769242817904719 223639009958653864226857079)
    ·
      refine ⟨335458514937980796340285619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223639009958653864226857079 335458514937980796340285619)
      ·
        refine ⟨503187772406971194510428429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335458514937980796340285619 503187772406971194510428429)
        ·
          refine ⟨188695414652614197941410661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503187772406971194510428429 188695414652614197941410661)
          ·
            refine ⟨35380390247365162114014499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188695414652614197941410661 35380390247365162114014499)
            ·
              refine ⟨53070585371047743171021749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35380390247365162114014499 53070585371047743171021749)
              ·
                refine ⟨4975367378535725922283289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53070585371047743171021749 4975367378535725922283289)
                ·
                  refine ⟨3731525533901794441712467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4975367378535725922283289 3731525533901794441712467)
                  ·
                    refine ⟨5597288300852691662568701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3731525533901794441712467 5597288300852691662568701)
                    ·
                      refine ⟨2098983112819759373463263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5597288300852691662568701 2098983112819759373463263)
                      ·
                        rfl

theorem cell23_4087755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 1, 3].length) (baseStart_4087755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087755 prefixEnd_4087755 := by exact prefixLift 4087755
  have htrace : WordTrace (prefixWord ++ tailWord_4087755) baseStart_4087755 baseEnd_4087755 := by
    simpa [prefixWord, tailWord_4087755, baseEnd_4087755] using wordTrace_append hprefix tailTrace_4087755
  have hstable : (prefixWord ++ tailWord_4087755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087755).length < 2 ^ (prefixWord ++ tailWord_4087755).sum := by decide
  have hdescent : baseEnd_4087755 < baseStart_4087755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087789 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4087789 : Nat := 118140960795 + 4087789 * 2 ^ 59
def prefixEnd_4087789 : Nat := 4983230072969 + 3 ^ 40 * 4087789 * 2
def baseEnd_4087789 : Nat := 2099000571162012240438107

theorem tailTrace_4087789 : CollatzResearch.WordTrace tailWord_4087789 prefixEnd_4087789 2099000571162012240438107 := by
  unfold tailWord_4087789
  simp only [CollatzResearch.WordTrace]
  refine ⟨149093913387646066624642421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99395942258430711083094947 149093913387646066624642421)
  ·
    refine ⟨13977554380091818746060227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149093913387646066624642421 13977554380091818746060227)
    ·
      refine ⟨20966331570137728119090341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13977554380091818746060227 20966331570137728119090341)
      ·
        refine ⟨3931187169400824022329439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20966331570137728119090341 3931187169400824022329439)
        ·
          refine ⟨5896780754101236033494159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931187169400824022329439 5896780754101236033494159)
          ·
            refine ⟨8845171131151854050241239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896780754101236033494159 8845171131151854050241239)
            ·
              refine ⟨13267756696727781075361859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8845171131151854050241239 13267756696727781075361859)
              ·
                refine ⟨19901635045091671613042789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13267756696727781075361859 19901635045091671613042789)
                ·
                  refine ⟨3731556570954688427445523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19901635045091671613042789 3731556570954688427445523)
                  ·
                    refine ⟨5597334856432032641168285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3731556570954688427445523 5597334856432032641168285)
                    ·
                      refine ⟨2099000571162012240438107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5597334856432032641168285 2099000571162012240438107)
                      ·
                        rfl

theorem cell23_4087789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4087789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087789 prefixEnd_4087789 := by exact prefixLift 4087789
  have htrace : WordTrace (prefixWord ++ tailWord_4087789) baseStart_4087789 baseEnd_4087789 := by
    simpa [prefixWord, tailWord_4087789, baseEnd_4087789] using wordTrace_append hprefix tailTrace_4087789
  have hstable : (prefixWord ++ tailWord_4087789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087789).length < 2 ^ (prefixWord ++ tailWord_4087789).sum := by decide
  have hdescent : baseEnd_4087789 < baseStart_4087789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087806 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_4087806 : Nat := 118140960795 + 4087806 * 2 ^ 59
def prefixEnd_4087806 : Nat := 4983230072969 + 3 ^ 40 * 4087806 * 2
def baseEnd_4087806 : Nat := 2099009300333138673925529

theorem tailTrace_4087806 : CollatzResearch.WordTrace tailWord_4087806 prefixEnd_4087806 2099009300333138673925529 := by
  unfold tailWord_4087806
  simp only [CollatzResearch.WordTrace]
  refine ⟨18636816678573059816001409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99396355619056319018674181 18636816678573059816001409)
  ·
    refine ⟨13977612508929794862001057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18636816678573059816001409 13977612508929794862001057)
    ·
      refine ⟨10483209381697346146500793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13977612508929794862001057 10483209381697346146500793)
      ·
        refine ⟨7862407036273009609875595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10483209381697346146500793 7862407036273009609875595)
        ·
          refine ⟨11793610554409514414813393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7862407036273009609875595 11793610554409514414813393)
          ·
            refine ⟨8845207915807135811110045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11793610554409514414813393 8845207915807135811110045)
            ·
              refine ⟨3316952968427675929166267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8845207915807135811110045 3316952968427675929166267)
              ·
                refine ⟨4975429452641513893749401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316952968427675929166267 4975429452641513893749401)
                ·
                  refine ⟨3731572089481135420312051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4975429452641513893749401 3731572089481135420312051)
                  ·
                    refine ⟨5597358134221703130468077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3731572089481135420312051 5597358134221703130468077)
                    ·
                      refine ⟨2099009300333138673925529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5597358134221703130468077 2099009300333138673925529)
                      ·
                        rfl

theorem cell23_4087806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_4087806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087806 prefixEnd_4087806 := by exact prefixLift 4087806
  have htrace : WordTrace (prefixWord ++ tailWord_4087806) baseStart_4087806 baseEnd_4087806 := by
    simpa [prefixWord, tailWord_4087806, baseEnd_4087806] using wordTrace_append hprefix tailTrace_4087806
  have hstable : (prefixWord ++ tailWord_4087806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087806).length < 2 ^ (prefixWord ++ tailWord_4087806).sum := by decide
  have hdescent : baseEnd_4087806 < baseStart_4087806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087811 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 9]
def baseStart_4087811 : Nat := 118140960795 + 4087811 * 2 ^ 59
def prefixEnd_4087811 : Nat := 4983230072969 + 3 ^ 40 * 4087811 * 2
def baseEnd_4087811 : Nat := 2099011867736411154363005

theorem tailTrace_4087811 : CollatzResearch.WordTrace tailWord_4087811 prefixEnd_4087811 2099011867736411154363005 := by
  unfold tailWord_4087811
  simp only [CollatzResearch.WordTrace]
  refine ⟨149094715793566364381943287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99396477195710909587962191 149094715793566364381943287)
  ·
    refine ⟨223642073690349546572914931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149094715793566364381943287 223642073690349546572914931)
    ·
      refine ⟨335463110535524319859372397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223642073690349546572914931 335463110535524319859372397)
      ·
        refine ⟨125798666450821619947264649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335463110535524319859372397 125798666450821619947264649)
        ·
          refine ⟨94348999838116214960448487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125798666450821619947264649 94348999838116214960448487)
          ·
            refine ⟨141523499757174322440672731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94348999838116214960448487 141523499757174322440672731)
            ·
              refine ⟨212285249635761483661009097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141523499757174322440672731 212285249635761483661009097)
              ·
                refine ⟨159213937226821112745756823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212285249635761483661009097 159213937226821112745756823)
                ·
                  refine ⟨238820905840231669118635235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159213937226821112745756823 238820905840231669118635235)
                  ·
                    refine ⟨358231358760347503677952853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238820905840231669118635235 358231358760347503677952853)
                    ·
                      refine ⟨2099011867736411154363005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 358231358760347503677952853 2099011867736411154363005)
                      ·
                        rfl

theorem cell23_4087811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_4087811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087811 prefixEnd_4087811 := by exact prefixLift 4087811
  have htrace : WordTrace (prefixWord ++ tailWord_4087811) baseStart_4087811 baseEnd_4087811 := by
    simpa [prefixWord, tailWord_4087811, baseEnd_4087811] using wordTrace_append hprefix tailTrace_4087811
  have hstable : (prefixWord ++ tailWord_4087811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087811).length < 2 ^ (prefixWord ++ tailWord_4087811).sum := by decide
  have hdescent : baseEnd_4087811 < baseStart_4087811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087858 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_4087858 : Nat := 118140960795 + 4087858 * 2 ^ 59
def prefixEnd_4087858 : Nat := 4983230072969 + 3 ^ 40 * 4087858 * 2
def baseEnd_4087858 : Nat := 2099036001327172470475289

theorem tailTrace_4087858 : CollatzResearch.WordTrace tailWord_4087858 prefixEnd_4087858 2099036001327172470475289 := by
  unfold tailWord_4087858
  simp only [CollatzResearch.WordTrace]
  refine ⟨37274107506099022852226057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99397620016264060939269485 37274107506099022852226057)
  ·
    refine ⟨27955580629574267139169543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37274107506099022852226057 27955580629574267139169543)
    ·
      refine ⟨41933370944361400708754315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27955580629574267139169543 41933370944361400708754315)
      ·
        refine ⟨62900056416542101063131473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41933370944361400708754315 62900056416542101063131473)
        ·
          refine ⟨47175042312406575797348605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62900056416542101063131473 47175042312406575797348605)
          ·
            refine ⟨17690640867152465924005727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47175042312406575797348605 17690640867152465924005727)
            ·
              refine ⟨26535961300728698886008591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17690640867152465924005727 26535961300728698886008591)
              ·
                refine ⟨39803941951093048329012887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26535961300728698886008591 39803941951093048329012887)
                ·
                  refine ⟨59705912926639572493519331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39803941951093048329012887 59705912926639572493519331)
                  ·
                    refine ⟨89558869389959358740278997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59705912926639572493519331 89558869389959358740278997)
                    ·
                      refine ⟨2099036001327172470475289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89558869389959358740278997 2099036001327172470475289)
                      ·
                        rfl

theorem cell23_4087858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_4087858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087858 prefixEnd_4087858 := by exact prefixLift 4087858
  have htrace : WordTrace (prefixWord ++ tailWord_4087858) baseStart_4087858 baseEnd_4087858 := by
    simpa [prefixWord, tailWord_4087858, baseEnd_4087858] using wordTrace_append hprefix tailTrace_4087858
  have hstable : (prefixWord ++ tailWord_4087858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087858).length < 2 ^ (prefixWord ++ tailWord_4087858).sum := by decide
  have hdescent : baseEnd_4087858 < baseStart_4087858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087898 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_4087898 : Nat := 118140960795 + 4087898 * 2 ^ 59
def prefixEnd_4087898 : Nat := 4983230072969 + 3 ^ 40 * 4087898 * 2
def baseEnd_4087898 : Nat := 2099056540553352313975105

theorem tailTrace_4087898 : CollatzResearch.WordTrace tailWord_4087898 prefixEnd_4087898 2099056540553352313975105 := by
  unfold tailWord_4087898
  simp only [CollatzResearch.WordTrace]
  refine ⟨37274472236062794560090087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99398592629500785493573565 37274472236062794560090087)
  ·
    refine ⟨55911708354094191840135131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37274472236062794560090087 55911708354094191840135131)
    ·
      refine ⟨83867562531141287760202697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55911708354094191840135131 83867562531141287760202697)
      ·
        refine ⟨62900671898355965820152023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83867562531141287760202697 62900671898355965820152023)
        ·
          refine ⟨94351007847533948730228035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62900671898355965820152023 94351007847533948730228035)
          ·
            refine ⟨141526511771300923095342053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94351007847533948730228035 141526511771300923095342053)
            ·
              refine ⟨26536220957118923080376635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141526511771300923095342053 26536220957118923080376635)
              ·
                refine ⟨39804331435678384620564953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26536220957118923080376635 39804331435678384620564953)
                ·
                  refine ⟨29853248576758788465423715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39804331435678384620564953 29853248576758788465423715)
                  ·
                    refine ⟨44779872865138182698135573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29853248576758788465423715 44779872865138182698135573)
                    ·
                      refine ⟨2099056540553352313975105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44779872865138182698135573 2099056540553352313975105)
                      ·
                        rfl

theorem cell23_4087898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_4087898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087898 prefixEnd_4087898 := by exact prefixLift 4087898
  have htrace : WordTrace (prefixWord ++ tailWord_4087898) baseStart_4087898 baseEnd_4087898 := by
    simpa [prefixWord, tailWord_4087898, baseEnd_4087898] using wordTrace_append hprefix tailTrace_4087898
  have hstable : (prefixWord ++ tailWord_4087898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087898).length < 2 ^ (prefixWord ++ tailWord_4087898).sum := by decide
  have hdescent : baseEnd_4087898 < baseStart_4087898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087908 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 8]
def baseStart_4087908 : Nat := 118140960795 + 4087908 * 2 ^ 59
def prefixEnd_4087908 : Nat := 4983230072969 + 3 ^ 40 * 4087908 * 2
def baseEnd_4087908 : Nat := 233229075039988586094451

theorem tailTrace_4087908 : CollatzResearch.WordTrace tailWord_4087908 prefixEnd_4087908 233229075039988586094451 := by
  unfold tailWord_4087908
  simp only [CollatzResearch.WordTrace]
  refine ⟨74549126837107474974112189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99398835782809966632149585 74549126837107474974112189)
  ·
    refine ⟨27955922563915303115292071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74549126837107474974112189 27955922563915303115292071)
    ·
      refine ⟨41933883845872954672938107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27955922563915303115292071 41933883845872954672938107)
      ·
        refine ⟨62900825768809432009407161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41933883845872954672938107 62900825768809432009407161)
        ·
          refine ⟨47175619326607074007055371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62900825768809432009407161 47175619326607074007055371)
          ·
            refine ⟨70763428989910611010583057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47175619326607074007055371 70763428989910611010583057)
            ·
              refine ⟨53072571742432958257937293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70763428989910611010583057 53072571742432958257937293)
              ·
                refine ⟨19902214403412359346726485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53072571742432958257937293 19902214403412359346726485)
                ·
                  refine ⟨233229075039988586094451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19902214403412359346726485 233229075039988586094451)
                  ·
                    rfl

theorem cell23_4087908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_4087908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087908 prefixEnd_4087908 := by exact prefixLift 4087908
  have htrace : WordTrace (prefixWord ++ tailWord_4087908) baseStart_4087908 baseEnd_4087908 := by
    simpa [prefixWord, tailWord_4087908, baseEnd_4087908] using wordTrace_append hprefix tailTrace_4087908
  have hstable : (prefixWord ++ tailWord_4087908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087908).length < 2 ^ (prefixWord ++ tailWord_4087908).sum := by decide
  have hdescent : baseEnd_4087908 < baseStart_4087908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087948 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_4087948 : Nat := 118140960795 + 4087948 * 2 ^ 59
def prefixEnd_4087948 : Nat := 4983230072969 + 3 ^ 40 * 4087948 * 2
def baseEnd_4087948 : Nat := 2099082214586077118349875

theorem tailTrace_4087948 : CollatzResearch.WordTrace tailWord_4087948 prefixEnd_4087948 2099082214586077118349875 := by
  unfold tailWord_4087948
  simp only [CollatzResearch.WordTrace]
  refine ⟨74549856297035018389840249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99399808396046691186453665 74549856297035018389840249)
  ·
    refine ⟨55912392222776263792380187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74549856297035018389840249 55912392222776263792380187)
    ·
      refine ⟨83868588334164395688570281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55912392222776263792380187 83868588334164395688570281)
      ·
        refine ⟨62901441250623296766427711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83868588334164395688570281 62901441250623296766427711)
        ·
          refine ⟨94352161875934945149641567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62901441250623296766427711 94352161875934945149641567)
          ·
            refine ⟨141528242813902417724462351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94352161875934945149641567 141528242813902417724462351)
            ·
              refine ⟨212292364220853626586693527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141528242813902417724462351 212292364220853626586693527)
              ·
                refine ⟨318438546331280439880040291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212292364220853626586693527 318438546331280439880040291)
                ·
                  refine ⟨477657819496920659820060437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318438546331280439880040291 477657819496920659820060437)
                  ·
                    refine ⟨22390210288918155929065333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 477657819496920659820060437 22390210288918155929065333)
                    ·
                      refine ⟨2099082214586077118349875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22390210288918155929065333 2099082214586077118349875)
                      ·
                        rfl

theorem cell23_4087948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_4087948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087948 prefixEnd_4087948 := by exact prefixLift 4087948
  have htrace : WordTrace (prefixWord ++ tailWord_4087948) baseStart_4087948 baseEnd_4087948 := by
    simpa [prefixWord, tailWord_4087948, baseEnd_4087948] using wordTrace_append hprefix tailTrace_4087948
  have hstable : (prefixWord ++ tailWord_4087948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087948).length < 2 ^ (prefixWord ++ tailWord_4087948).sum := by decide
  have hdescent : baseEnd_4087948 < baseStart_4087948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087959 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 6]
def baseStart_4087959 : Nat := 118140960795 + 4087959 * 2 ^ 59
def prefixEnd_4087959 : Nat := 4983230072969 + 3 ^ 40 * 4087959 * 2
def baseEnd_4087959 : Nat := 233231984763697397256925

theorem tailTrace_4087959 : CollatzResearch.WordTrace tailWord_4087959 prefixEnd_4087959 233231984763697397256925 := by
  unfold tailWord_4087959
  simp only [CollatzResearch.WordTrace]
  refine ⟨149100113797030185658330931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99400075864686790438887287 149100113797030185658330931)
  ·
    refine ⟨223650170695545278487496397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149100113797030185658330931 223650170695545278487496397)
    ·
      refine ⟨83868814010829479432811149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223650170695545278487496397 83868814010829479432811149)
      ·
        refine ⟨31450805254061054787304181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83868814010829479432811149 31450805254061054787304181)
        ·
          refine ⟨2948512992568223886309767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31450805254061054787304181 2948512992568223886309767)
          ·
            refine ⟨4422769488852335829464651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948512992568223886309767 4422769488852335829464651)
            ·
              refine ⟨6634154233278503744196977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4422769488852335829464651 6634154233278503744196977)
              ·
                refine ⟨4975615674958877808147733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6634154233278503744196977 4975615674958877808147733)
                ·
                  refine ⟨233231984763697397256925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4975615674958877808147733 233231984763697397256925)
                  ·
                    rfl

theorem cell23_4087959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 6].length) (baseStart_4087959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087959 prefixEnd_4087959 := by exact prefixLift 4087959
  have htrace : WordTrace (prefixWord ++ tailWord_4087959) baseStart_4087959 baseEnd_4087959 := by
    simpa [prefixWord, tailWord_4087959, baseEnd_4087959] using wordTrace_append hprefix tailTrace_4087959
  have hstable : (prefixWord ++ tailWord_4087959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087959).length < 2 ^ (prefixWord ++ tailWord_4087959).sum := by decide
  have hdescent : baseEnd_4087959 < baseStart_4087959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087969 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_4087969 : Nat := 118140960795 + 4087969 * 2 ^ 59
def prefixEnd_4087969 : Nat := 4983230072969 + 3 ^ 40 * 4087969 * 2
def baseEnd_4087969 : Nat := 2099092997679821536187279

theorem tailTrace_4087969 : CollatzResearch.WordTrace tailWord_4087969 prefixEnd_4087969 2099092997679821536187279 := by
  unfold tailWord_4087969
  simp only [CollatzResearch.WordTrace]
  refine ⟨149100478526993957366194961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99400319017995971577463307 149100478526993957366194961)
  ·
    refine ⟨111825358895245468024646221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149100478526993957366194961 111825358895245468024646221)
    ·
      refine ⟨41934509585717050509242333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111825358895245468024646221 41934509585717050509242333)
      ·
        refine ⟨15725441094643893940965875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41934509585717050509242333 15725441094643893940965875)
        ·
          refine ⟨23588161641965840911448813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15725441094643893940965875 23588161641965840911448813)
          ·
            refine ⟨8845560615737190341793305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23588161641965840911448813 8845560615737190341793305)
            ·
              refine ⟨6634170461802892756344979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8845560615737190341793305 6634170461802892756344979)
              ·
                refine ⟨9951255692704339134517469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634170461802892756344979 9951255692704339134517469)
                ·
                  refine ⟨3731720884764127175444051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9951255692704339134517469 3731720884764127175444051)
                  ·
                    refine ⟨5597581327146190763166077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3731720884764127175444051 5597581327146190763166077)
                    ·
                      refine ⟨2099092997679821536187279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5597581327146190763166077 2099092997679821536187279)
                      ·
                        rfl

theorem cell23_4087969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_4087969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087969 prefixEnd_4087969 := by exact prefixLift 4087969
  have htrace : WordTrace (prefixWord ++ tailWord_4087969) baseStart_4087969 baseEnd_4087969 := by
    simpa [prefixWord, tailWord_4087969, baseEnd_4087969] using wordTrace_append hprefix tailTrace_4087969
  have hstable : (prefixWord ++ tailWord_4087969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087969).length < 2 ^ (prefixWord ++ tailWord_4087969).sum := by decide
  have hdescent : baseEnd_4087969 < baseStart_4087969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4087992 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 1, 1, 4]
def baseStart_4087992 : Nat := 118140960795 + 4087992 * 2 ^ 59
def prefixEnd_4087992 : Nat := 4983230072969 + 3 ^ 40 * 4087992 * 2
def baseEnd_4087992 : Nat := 2099104807734874946199673

theorem tailTrace_4087992 : CollatzResearch.WordTrace tailWord_4087992 prefixEnd_4087992 2099104807734874946199673 := by
  unfold tailWord_4087992
  simp only [CollatzResearch.WordTrace]
  refine ⟨74550658702955316147141115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99400878270607088196188153 74550658702955316147141115)
  ·
    refine ⟨111825988054432974220711673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74550658702955316147141115 111825988054432974220711673)
    ·
      refine ⟨83869491040824730665533755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111825988054432974220711673 83869491040824730665533755)
      ·
        refine ⟨125804236561237095998300633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83869491040824730665533755 125804236561237095998300633)
        ·
          refine ⟨94353177420927821998725475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125804236561237095998300633 94353177420927821998725475)
          ·
            refine ⟨141529766131391732998088213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94353177420927821998725475 141529766131391732998088213)
            ·
              refine ⟨6634207787408987484285385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141529766131391732998088213 6634207787408987484285385)
              ·
                refine ⟨4975655840556740613214039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6634207787408987484285385 4975655840556740613214039)
                ·
                  refine ⟨7463483760835110919821059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4975655840556740613214039 7463483760835110919821059)
                  ·
                    refine ⟨11195225641252666379731589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7463483760835110919821059 11195225641252666379731589)
                    ·
                      refine ⟨2099104807734874946199673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11195225641252666379731589 2099104807734874946199673)
                      ·
                        rfl

theorem cell23_4087992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_4087992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4087992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4087992 prefixEnd_4087992 := by exact prefixLift 4087992
  have htrace : WordTrace (prefixWord ++ tailWord_4087992) baseStart_4087992 baseEnd_4087992 := by
    simpa [prefixWord, tailWord_4087992, baseEnd_4087992] using wordTrace_append hprefix tailTrace_4087992
  have hstable : (prefixWord ++ tailWord_4087992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4087992).length < 2 ^ (prefixWord ++ tailWord_4087992).sum := by decide
  have hdescent : baseEnd_4087992 < baseStart_4087992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4087992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088005 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_4088005 : Nat := 118140960795 + 4088005 * 2 ^ 59
def prefixEnd_4088005 : Nat := 4983230072969 + 3 ^ 40 * 4088005 * 2
def baseEnd_4088005 : Nat := 2099111482983383395337113

theorem tailTrace_4088005 : CollatzResearch.WordTrace tailWord_4088005 prefixEnd_4088005 2099111482983383395337113 := by
  unfold tailWord_4088005
  simp only [CollatzResearch.WordTrace]
  refine ⟨149101791554863535514505469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99401194369909023676336979 149101791554863535514505469)
  ·
    refine ⟨55913171833073825817939551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149101791554863535514505469 55913171833073825817939551)
    ·
      refine ⟨83869757749610738726909327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55913171833073825817939551 83869757749610738726909327)
      ·
        refine ⟨125804636624416108090363991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83869757749610738726909327 125804636624416108090363991)
        ·
          refine ⟨188706954936624162135545987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125804636624416108090363991 188706954936624162135545987)
          ·
            refine ⟨283060432404936243203318981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188706954936624162135545987 283060432404936243203318981)
            ·
              refine ⟨53073831075925545600622309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283060432404936243203318981 53073831075925545600622309)
              ·
                refine ⟨9951343326736039800116683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53073831075925545600622309 9951343326736039800116683)
                ·
                  refine ⟨14927014990104059700175025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9951343326736039800116683 14927014990104059700175025)
                  ·
                    refine ⟨11195261242578044775131269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14927014990104059700175025 11195261242578044775131269)
                    ·
                      refine ⟨2099111482983383395337113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11195261242578044775131269 2099111482983383395337113)
                      ·
                        rfl

theorem cell23_4088005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_4088005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088005 prefixEnd_4088005 := by exact prefixLift 4088005
  have htrace : WordTrace (prefixWord ++ tailWord_4088005) baseStart_4088005 baseEnd_4088005 := by
    simpa [prefixWord, tailWord_4088005, baseEnd_4088005] using wordTrace_append hprefix tailTrace_4088005
  have hstable : (prefixWord ++ tailWord_4088005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088005).length < 2 ^ (prefixWord ++ tailWord_4088005).sum := by decide
  have hdescent : baseEnd_4088005 < baseStart_4088005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088026 : List Nat := [3, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2]
def baseStart_4088026 : Nat := 118140960795 + 4088026 * 2 ^ 59
def prefixEnd_4088026 : Nat := 4983230072969 + 3 ^ 40 * 4088026 * 2
def baseEnd_4088026 : Nat := 2099122266077127813174517

theorem tailTrace_4088026 : CollatzResearch.WordTrace tailWord_4088026 prefixEnd_4088026 2099122266077127813174517 := by
  unfold tailWord_4088026
  simp only [CollatzResearch.WordTrace]
  refine ⟨37275639371946864025254983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99401704991858304067346621 37275639371946864025254983)
  ·
    refine ⟨55913459057920296037882475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37275639371946864025254983 55913459057920296037882475)
    ·
      refine ⟨83870188586880444056823713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55913459057920296037882475 83870188586880444056823713)
      ·
        refine ⟨62902641440160333042617785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83870188586880444056823713 62902641440160333042617785)
        ·
          refine ⟨47176981080120249781963339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62902641440160333042617785 47176981080120249781963339)
          ·
            refine ⟨70765471620180374672945009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47176981080120249781963339 70765471620180374672945009)
            ·
              refine ⟨53074103715135281004708757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70765471620180374672945009 53074103715135281004708757)
              ·
                refine ⟨2487848611646966297095723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53074103715135281004708757 2487848611646966297095723)
                ·
                  refine ⟨3731772917470449445643585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487848611646966297095723 3731772917470449445643585)
                  ·
                    refine ⟨2798829688102837084232689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3731772917470449445643585 2798829688102837084232689)
                    ·
                      refine ⟨2099122266077127813174517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2798829688102837084232689 2099122266077127813174517)
                      ·
                        rfl

theorem cell23_4088026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_4088026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088026 prefixEnd_4088026 := by exact prefixLift 4088026
  have htrace : WordTrace (prefixWord ++ tailWord_4088026) baseStart_4088026 baseEnd_4088026 := by
    simpa [prefixWord, tailWord_4088026, baseEnd_4088026] using wordTrace_append hprefix tailTrace_4088026
  have hstable : (prefixWord ++ tailWord_4088026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088026).length < 2 ^ (prefixWord ++ tailWord_4088026).sum := by decide
  have hdescent : baseEnd_4088026 < baseStart_4088026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088042 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_4088042 : Nat := 118140960795 + 4088042 * 2 ^ 59
def prefixEnd_4088042 : Nat := 4983230072969 + 3 ^ 40 * 4088042 * 2
def baseEnd_4088042 : Nat := 2099130481767599750574443

theorem tailTrace_4088042 : CollatzResearch.WordTrace tailWord_4088042 prefixEnd_4088042 2099130481767599750574443 := by
  unfold tailWord_4088042
  simp only [CollatzResearch.WordTrace]
  refine ⟨37275785263932372708400595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99402094037152993889068253 37275785263932372708400595)
  ·
    refine ⟨55913677895898559062600893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37275785263932372708400595 55913677895898559062600893)
    ·
      refine ⟨20967629210961959648475335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55913677895898559062600893 20967629210961959648475335)
      ·
        refine ⟨31451443816442939472713003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20967629210961959648475335 31451443816442939472713003)
        ·
          refine ⟨47177165724664409209069505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31451443816442939472713003 47177165724664409209069505)
          ·
            refine ⟨35382874293498306906802129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47177165724664409209069505 35382874293498306906802129)
            ·
              refine ⟨26537155720123730180101597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35382874293498306906802129 26537155720123730180101597)
              ·
                refine ⟨9951433395046398817538099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26537155720123730180101597 9951433395046398817538099)
                ·
                  refine ⟨14927150092569598226307149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9951433395046398817538099 14927150092569598226307149)
                  ·
                    refine ⟨5597681284713599334865181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14927150092569598226307149 5597681284713599334865181)
                    ·
                      refine ⟨2099130481767599750574443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5597681284713599334865181 2099130481767599750574443)
                      ·
                        rfl

theorem cell23_4088042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_4088042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088042 prefixEnd_4088042 := by exact prefixLift 4088042
  have htrace : WordTrace (prefixWord ++ tailWord_4088042) baseStart_4088042 baseEnd_4088042 := by
    simpa [prefixWord, tailWord_4088042, baseEnd_4088042] using wordTrace_append hprefix tailTrace_4088042
  have hstable : (prefixWord ++ tailWord_4088042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088042).length < 2 ^ (prefixWord ++ tailWord_4088042).sum := by decide
  have hdescent : baseEnd_4088042 < baseStart_4088042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088075 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 2, 6]
def baseStart_4088075 : Nat := 118140960795 + 4088075 * 2 ^ 59
def prefixEnd_4088075 : Nat := 4983230072969 + 3 ^ 40 * 4088075 * 2
def baseEnd_4088075 : Nat := 699715808876399373820597

theorem tailTrace_4088075 : CollatzResearch.WordTrace tailWord_4088075 prefixEnd_4088075 699715808876399373820597 := by
  unfold tailWord_4088075
  simp only [CollatzResearch.WordTrace]
  refine ⟨149104344664609937469553679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99402896443073291646369119 149104344664609937469553679)
  ·
    refine ⟨223656516996914906204330519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149104344664609937469553679 223656516996914906204330519)
    ·
      refine ⟨335484775495372359306495779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223656516996914906204330519 335484775495372359306495779)
      ·
        refine ⟨503227163243058538959743669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335484775495372359306495779 503227163243058538959743669)
        ·
          refine ⟨47177546554036738027475969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 503227163243058538959743669 47177546554036738027475969)
          ·
            refine ⟨35383159915527553520606977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47177546554036738027475969 35383159915527553520606977)
            ·
              refine ⟨26537369936645665140455233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35383159915527553520606977 26537369936645665140455233)
              ·
                refine ⟨19903027452484248855341425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26537369936645665140455233 19903027452484248855341425)
                ·
                  refine ⟨14927270589363186641506069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19903027452484248855341425 14927270589363186641506069)
                  ·
                    refine ⟨699715808876399373820597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14927270589363186641506069 699715808876399373820597)
                    ·
                      rfl

theorem cell23_4088075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 6].length) (baseStart_4088075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088075 prefixEnd_4088075 := by exact prefixLift 4088075
  have htrace : WordTrace (prefixWord ++ tailWord_4088075) baseStart_4088075 baseEnd_4088075 := by
    simpa [prefixWord, tailWord_4088075, baseEnd_4088075] using wordTrace_append hprefix tailTrace_4088075
  have hstable : (prefixWord ++ tailWord_4088075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088075).length < 2 ^ (prefixWord ++ tailWord_4088075).sum := by decide
  have hdescent : baseEnd_4088075 < baseStart_4088075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088085 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_4088085 : Nat := 118140960795 + 4088085 * 2 ^ 59
def prefixEnd_4088085 : Nat := 4983230072969 + 3 ^ 40 * 4088085 * 2
def baseEnd_4088085 : Nat := 2099152561435743082336745

theorem tailTrace_4088085 : CollatzResearch.WordTrace tailWord_4088085 prefixEnd_4088085 2099152561435743082336745 := by
  unfold tailWord_4088085
  simp only [CollatzResearch.WordTrace]
  refine ⟨149104709394573709177417709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99403139596382472784945139 149104709394573709177417709)
  ·
    refine ⟨55914266022965140941531641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149104709394573709177417709 55914266022965140941531641)
    ·
      refine ⟨41935699517223855706148731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55914266022965140941531641 41935699517223855706148731)
      ·
        refine ⟨62903549275835783559223097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41935699517223855706148731 62903549275835783559223097)
        ·
          refine ⟨47177661956876837669417323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62903549275835783559223097 47177661956876837669417323)
          ·
            refine ⟨70766492935315256504125985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47177661956876837669417323 70766492935315256504125985)
            ·
              refine ⟨53074869701486442378094489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70766492935315256504125985 53074869701486442378094489)
              ·
                refine ⟨39806152276114831783570867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53074869701486442378094489 39806152276114831783570867)
                ·
                  refine ⟨59709228414172247675356301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39806152276114831783570867 59709228414172247675356301)
                  ·
                    refine ⟨22390960655314592878258613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59709228414172247675356301 22390960655314592878258613)
                    ·
                      refine ⟨2099152561435743082336745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22390960655314592878258613 2099152561435743082336745)
                      ·
                        rfl

theorem cell23_4088085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_4088085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088085 prefixEnd_4088085 := by exact prefixLift 4088085
  have htrace : WordTrace (prefixWord ++ tailWord_4088085) baseStart_4088085 baseEnd_4088085 := by
    simpa [prefixWord, tailWord_4088085, baseEnd_4088085] using wordTrace_append hprefix tailTrace_4088085
  have hstable : (prefixWord ++ tailWord_4088085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088085).length < 2 ^ (prefixWord ++ tailWord_4088085).sum := by decide
  have hdescent : baseEnd_4088085 < baseStart_4088085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088099 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 1, 4, 2]
def baseStart_4088099 : Nat := 118140960795 + 4088099 * 2 ^ 59
def prefixEnd_4088099 : Nat := 4983230072969 + 3 ^ 40 * 4088099 * 2
def baseEnd_4088099 : Nat := 2099159750164906027561681

theorem tailTrace_4088099 : CollatzResearch.WordTrace tailWord_4088099 prefixEnd_4088099 2099159750164906027561681 := by
  unfold tailWord_4088099
  simp only [CollatzResearch.WordTrace]
  refine ⟨149105220016522989568427351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99403480011015326378951567 149105220016522989568427351)
  ·
    refine ⟨223657830024784484352641027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149105220016522989568427351 223657830024784484352641027)
    ·
      refine ⟨335486745037176726528961541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223657830024784484352641027 335486745037176726528961541)
      ·
        refine ⟨62903764694470636224180289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335486745037176726528961541 62903764694470636224180289)
        ·
          refine ⟨47177823520852977168135217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62903764694470636224180289 47177823520852977168135217)
          ·
            refine ⟨35383367640639732876101413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47177823520852977168135217 35383367640639732876101413)
            ·
              refine ⟨6634381432619949914269015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35383367640639732876101413 6634381432619949914269015)
              ·
                refine ⟨9951572148929924871403523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634381432619949914269015 9951572148929924871403523)
                ·
                  refine ⟨14927358223394887307105285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9951572148929924871403523 14927358223394887307105285)
                  ·
                    refine ⟨2798879666886541370082241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14927358223394887307105285 2798879666886541370082241)
                    ·
                      refine ⟨2099159750164906027561681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2798879666886541370082241 2099159750164906027561681)
                      ·
                        rfl

theorem cell23_4088099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_4088099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088099 prefixEnd_4088099 := by exact prefixLift 4088099
  have htrace : WordTrace (prefixWord ++ tailWord_4088099) baseStart_4088099 baseEnd_4088099 := by
    simpa [prefixWord, tailWord_4088099, baseEnd_4088099] using wordTrace_append hprefix tailTrace_4088099
  have hstable : (prefixWord ++ tailWord_4088099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088099).length < 2 ^ (prefixWord ++ tailWord_4088099).sum := by decide
  have hdescent : baseEnd_4088099 < baseStart_4088099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088116 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_4088116 : Nat := 118140960795 + 4088116 * 2 ^ 59
def prefixEnd_4088116 : Nat := 4983230072969 + 3 ^ 40 * 4088116 * 2
def baseEnd_4088116 : Nat := 2099168479336032461049103

theorem tailTrace_4088116 : CollatzResearch.WordTrace tailWord_4088116 prefixEnd_4088116 2099168479336032461049103 := by
  unfold tailWord_4088116
  simp only [CollatzResearch.WordTrace]
  refine ⟨74552920028730700735898101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99403893371640934314530801 74552920028730700735898101)
  ·
    refine ⟨6989336252693503193990447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74552920028730700735898101 6989336252693503193990447)
    ·
      refine ⟨10484004379040254790985671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6989336252693503193990447 10484004379040254790985671)
      ·
        refine ⟨15726006568560382186478507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10484004379040254790985671 15726006568560382186478507)
        ·
          refine ⟨23589009852840573279717761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15726006568560382186478507 23589009852840573279717761)
          ·
            refine ⟨17691757389630429959788321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23589009852840573279717761 17691757389630429959788321)
            ·
              refine ⟨13268818042222822469841241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17691757389630429959788321 13268818042222822469841241)
              ·
                refine ⟨9951613531667116852380931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13268818042222822469841241 9951613531667116852380931)
                ·
                  refine ⟨14927420297500675278571397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9951613531667116852380931 14927420297500675278571397)
                  ·
                    refine ⟨2798891305781376614732137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14927420297500675278571397 2798891305781376614732137)
                    ·
                      refine ⟨2099168479336032461049103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2798891305781376614732137 2099168479336032461049103)
                      ·
                        rfl

theorem cell23_4088116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_4088116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088116 prefixEnd_4088116 := by exact prefixLift 4088116
  have htrace : WordTrace (prefixWord ++ tailWord_4088116) baseStart_4088116 baseEnd_4088116 := by
    simpa [prefixWord, tailWord_4088116, baseEnd_4088116] using wordTrace_append hprefix tailTrace_4088116
  have hstable : (prefixWord ++ tailWord_4088116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088116).length < 2 ^ (prefixWord ++ tailWord_4088116).sum := by decide
  have hdescent : baseEnd_4088116 < baseStart_4088116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088189 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_4088189 : Nat := 118140960795 + 4088189 * 2 ^ 59
def prefixEnd_4088189 : Nat := 4983230072969 + 3 ^ 40 * 4088189 * 2
def baseEnd_4088189 : Nat := 2099205963423810675436267

theorem tailTrace_4088189 : CollatzResearch.WordTrace tailWord_4088189 prefixEnd_4088189 2099205963423810675436267 := by
  unfold tailWord_4088189
  simp only [CollatzResearch.WordTrace]
  refine ⟨149108502586196934939203621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99405668390797956626135747 149108502586196934939203621)
  ·
    refine ⟨27957844234911925301100679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149108502586196934939203621 27957844234911925301100679)
    ·
      refine ⟨41936766352367887951651019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27957844234911925301100679 41936766352367887951651019)
      ·
        refine ⟨62905149528551831927476529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41936766352367887951651019 62905149528551831927476529)
        ·
          refine ⟨47178862146413873945607397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62905149528551831927476529 47178862146413873945607397)
          ·
            refine ⟨8846036652452601364801387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47178862146413873945607397 8846036652452601364801387)
            ·
              refine ⟨13269054978678902047202081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8846036652452601364801387 13269054978678902047202081)
              ·
                refine ⟨9951791234009176535401561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13269054978678902047202081 9951791234009176535401561)
                ·
                  refine ⟨7463843425506882401551171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9951791234009176535401561 7463843425506882401551171)
                  ·
                    refine ⟨11195765138260323602326757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7463843425506882401551171 11195765138260323602326757)
                    ·
                      refine ⟨2099205963423810675436267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11195765138260323602326757 2099205963423810675436267)
                      ·
                        rfl

theorem cell23_4088189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_4088189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088189 prefixEnd_4088189 := by exact prefixLift 4088189
  have htrace : WordTrace (prefixWord ++ tailWord_4088189) baseStart_4088189 baseEnd_4088189 := by
    simpa [prefixWord, tailWord_4088189, baseEnd_4088189] using wordTrace_append hprefix tailTrace_4088189
  have hstable : (prefixWord ++ tailWord_4088189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088189).length < 2 ^ (prefixWord ++ tailWord_4088189).sum := by decide
  have hdescent : baseEnd_4088189 < baseStart_4088189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088226 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_4088226 : Nat := 118140960795 + 4088226 * 2 ^ 59
def prefixEnd_4088226 : Nat := 4983230072969 + 3 ^ 40 * 4088226 * 2
def baseEnd_4088226 : Nat := 2099224962208027030673597

theorem tailTrace_4088226 : CollatzResearch.WordTrace tailWord_4088226 prefixEnd_4088226 2099224962208027030673597 := by
  unfold tailWord_4088226
  simp only [CollatzResearch.WordTrace]
  refine ⟨37277463021765722564575133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99406568058041926838867021 37277463021765722564575133)
  ·
    refine ⟨13979048633162145961715675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37277463021765722564575133 13979048633162145961715675)
    ·
      refine ⟨20968572949743218942573513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13979048633162145961715675 20968572949743218942573513)
      ·
        refine ⟨15726429712307414206930135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20968572949743218942573513 15726429712307414206930135)
        ·
          refine ⟨23589644568461121310395203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15726429712307414206930135 23589644568461121310395203)
          ·
            refine ⟨35384466852691681965592805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23589644568461121310395203 35384466852691681965592805)
            ·
              refine ⟨6634587534879690368548651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35384466852691681965592805 6634587534879690368548651)
              ·
                refine ⟨9951881302319535552822977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634587534879690368548651 9951881302319535552822977)
                ·
                  refine ⟨7463910976739651664617233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9951881302319535552822977 7463910976739651664617233)
                  ·
                    refine ⟨5597933232554738748462925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7463910976739651664617233 5597933232554738748462925)
                    ·
                      refine ⟨2099224962208027030673597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5597933232554738748462925 2099224962208027030673597)
                      ·
                        rfl

theorem cell23_4088226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_4088226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088226 prefixEnd_4088226 := by exact prefixLift 4088226
  have htrace : WordTrace (prefixWord ++ tailWord_4088226) baseStart_4088226 baseEnd_4088226 := by
    simpa [prefixWord, tailWord_4088226, baseEnd_4088226] using wordTrace_append hprefix tailTrace_4088226
  have hstable : (prefixWord ++ tailWord_4088226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088226).length < 2 ^ (prefixWord ++ tailWord_4088226).sum := by decide
  have hdescent : baseEnd_4088226 < baseStart_4088226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088289 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 4, 4]
def baseStart_4088289 : Nat := 118140960795 + 4088289 * 2 ^ 59
def prefixEnd_4088289 : Nat := 4983230072969 + 3 ^ 40 * 4088289 * 2
def baseEnd_4088289 : Nat := 699752437163086761395269

theorem tailTrace_4088289 : CollatzResearch.WordTrace tailWord_4088289 prefixEnd_4088289 699752437163086761395269 := by
  unfold tailWord_4088289
  simp only [CollatzResearch.WordTrace]
  refine ⟨149112149885834652017843921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99408099923889768011895947 149112149885834652017843921)
  ·
    refine ⟨111834112414375989013382941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149112149885834652017843921 111834112414375989013382941)
    ·
      refine ⟨41937792155390995880018603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111834112414375989013382941 41937792155390995880018603)
      ·
        refine ⟨62906688233086493820027905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41937792155390995880018603 62906688233086493820027905)
        ·
          refine ⟨47180016174814870365020929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62906688233086493820027905 47180016174814870365020929)
          ·
            refine ⟨35385012131111152773765697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47180016174814870365020929 35385012131111152773765697)
            ·
              refine ⟨26538759098333364580324273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35385012131111152773765697 26538759098333364580324273)
              ·
                refine ⟨19904069323750023435243205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26538759098333364580324273 19904069323750023435243205)
                ·
                  refine ⟨3732012998203129394108101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19904069323750023435243205 3732012998203129394108101)
                  ·
                    refine ⟨699752437163086761395269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3732012998203129394108101 699752437163086761395269)
                    ·
                      rfl

theorem cell23_4088289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_4088289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088289 prefixEnd_4088289 := by exact prefixLift 4088289
  have htrace : WordTrace (prefixWord ++ tailWord_4088289) baseStart_4088289 baseEnd_4088289 := by
    simpa [prefixWord, tailWord_4088289, baseEnd_4088289] using wordTrace_append hprefix tailTrace_4088289
  have hstable : (prefixWord ++ tailWord_4088289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088289).length < 2 ^ (prefixWord ++ tailWord_4088289).sum := by decide
  have hdescent : baseEnd_4088289 < baseStart_4088289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088292 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_4088292 : Nat := 118140960795 + 4088292 * 2 ^ 59
def prefixEnd_4088292 : Nat := 4983230072969 + 3 ^ 40 * 4088292 * 2
def baseEnd_4088292 : Nat := 2099258851931223772448293

theorem tailTrace_4088292 : CollatzResearch.WordTrace tailWord_4088292 prefixEnd_4088292 2099258851931223772448293 := by
  unfold tailWord_4088292
  simp only [CollatzResearch.WordTrace]
  refine ⟨74556129652411891765101565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99408172869882522353468753 74556129652411891765101565)
  ·
    refine ⟨27958548619654459411913087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74556129652411891765101565 27958548619654459411913087)
    ·
      refine ⟨41937822929481689117869631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27958548619654459411913087 41937822929481689117869631)
      ·
        refine ⟨62906734394222533676804447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41937822929481689117869631 62906734394222533676804447)
        ·
          refine ⟨94360101591333800515206671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62906734394222533676804447 94360101591333800515206671)
          ·
            refine ⟨141540152387000700772810007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94360101591333800515206671 141540152387000700772810007)
            ·
              refine ⟨212310228580501051159215011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141540152387000700772810007 212310228580501051159215011)
              ·
                refine ⟨318465342870751576738822517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212310228580501051159215011 318465342870751576738822517)
                ·
                  refine ⟨29856125894132960319264611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318465342870751576738822517 29856125894132960319264611)
                  ·
                    refine ⟨44784188841199440478896917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29856125894132960319264611 44784188841199440478896917)
                    ·
                      refine ⟨2099258851931223772448293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44784188841199440478896917 2099258851931223772448293)
                      ·
                        rfl

theorem cell23_4088292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_4088292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088292 prefixEnd_4088292 := by exact prefixLift 4088292
  have htrace : WordTrace (prefixWord ++ tailWord_4088292) baseStart_4088292 baseEnd_4088292 := by
    simpa [prefixWord, tailWord_4088292, baseEnd_4088292] using wordTrace_append hprefix tailTrace_4088292
  have hstable : (prefixWord ++ tailWord_4088292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088292).length < 2 ^ (prefixWord ++ tailWord_4088292).sum := by decide
  have hdescent : baseEnd_4088292 < baseStart_4088292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088296 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_4088296 : Nat := 118140960795 + 4088296 * 2 ^ 59
def prefixEnd_4088296 : Nat := 4983230072969 + 3 ^ 40 * 4088296 * 2
def baseEnd_4088296 : Nat := 2099260905853841756798275

theorem tailTrace_4088296 : CollatzResearch.WordTrace tailWord_4088296 prefixEnd_4088296 2099260905853841756798275 := by
  unfold tailWord_4088296
  simp only [CollatzResearch.WordTrace]
  refine ⟨74556202598404646106674371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99408270131206194808899161 74556202598404646106674371)
  ·
    refine ⟨111834303897606969160011557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74556202598404646106674371 111834303897606969160011557)
    ·
      refine ⟨20968931980801306717502167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111834303897606969160011557 20968931980801306717502167)
      ·
        refine ⟨31453397971201960076253251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20968931980801306717502167 31453397971201960076253251)
        ·
          refine ⟨47180096956802940114379877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31453397971201960076253251 47180096956802940114379877)
          ·
            refine ⟨8846268179400551271446227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47180096956802940114379877 8846268179400551271446227)
            ·
              refine ⟨13269402269100826907169341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8846268179400551271446227 13269402269100826907169341)
              ·
                refine ⟨4976025850912810090188503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13269402269100826907169341 4976025850912810090188503)
                ·
                  refine ⟨7464038776369215135282755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976025850912810090188503 7464038776369215135282755)
                  ·
                    refine ⟨11196058164553822702924133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464038776369215135282755 11196058164553822702924133)
                    ·
                      refine ⟨2099260905853841756798275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11196058164553822702924133 2099260905853841756798275)
                      ·
                        rfl

theorem cell23_4088296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_4088296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088296 prefixEnd_4088296 := by exact prefixLift 4088296
  have htrace : WordTrace (prefixWord ++ tailWord_4088296) baseStart_4088296 baseEnd_4088296 := by
    simpa [prefixWord, tailWord_4088296, baseEnd_4088296] using wordTrace_append hprefix tailTrace_4088296
  have hstable : (prefixWord ++ tailWord_4088296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088296).length < 2 ^ (prefixWord ++ tailWord_4088296).sum := by decide
  have hdescent : baseEnd_4088296 < baseStart_4088296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088329 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 1, 3, 3]
def baseStart_4088329 : Nat := 118140960795 + 4088329 * 2 ^ 59
def prefixEnd_4088329 : Nat := 4983230072969 + 3 ^ 40 * 4088329 * 2
def baseEnd_4088329 : Nat := 2099277850715440127685623

theorem tailTrace_4088329 : CollatzResearch.WordTrace tailWord_4088329 prefixEnd_4088329 2099277850715440127685623 := by
  unfold tailWord_4088329
  simp only [CollatzResearch.WordTrace]
  refine ⟨149113608805689738849300041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99409072537126492566200027 149113608805689738849300041)
  ·
    refine ⟨111835206604267304136975031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149113608805689738849300041 111835206604267304136975031)
    ·
      refine ⟨167752809906400956205462547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111835206604267304136975031 167752809906400956205462547)
      ·
        refine ⟨251629214859601434308193821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167752809906400956205462547 251629214859601434308193821)
        ·
          refine ⟨94360955572350537865572683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251629214859601434308193821 94360955572350537865572683)
          ·
            refine ⟨141541433358525806798359025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94360955572350537865572683 141541433358525806798359025)
            ·
              refine ⟨106156075018894355098769269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141541433358525806798359025 106156075018894355098769269)
              ·
                refine ⟨9952132033021345790509619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106156075018894355098769269 9952132033021345790509619)
                ·
                  refine ⟨14928198049532018685764429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9952132033021345790509619 14928198049532018685764429)
                  ·
                    refine ⟨5598074268574507007161661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14928198049532018685764429 5598074268574507007161661)
                    ·
                      refine ⟨2099277850715440127685623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5598074268574507007161661 2099277850715440127685623)
                      ·
                        rfl

theorem cell23_4088329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3, 3].length) (baseStart_4088329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088329 prefixEnd_4088329 := by exact prefixLift 4088329
  have htrace : WordTrace (prefixWord ++ tailWord_4088329) baseStart_4088329 baseEnd_4088329 := by
    simpa [prefixWord, tailWord_4088329, baseEnd_4088329] using wordTrace_append hprefix tailTrace_4088329
  have hstable : (prefixWord ++ tailWord_4088329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088329).length < 2 ^ (prefixWord ++ tailWord_4088329).sum := by decide
  have hdescent : baseEnd_4088329 < baseStart_4088329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088346 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3]
def baseStart_4088346 : Nat := 118140960795 + 4088346 * 2 ^ 59
def prefixEnd_4088346 : Nat := 4983230072969 + 3 ^ 40 * 4088346 * 2
def baseEnd_4088346 : Nat := 2099286579886566561173045

theorem tailTrace_4088346 : CollatzResearch.WordTrace tailWord_4088346 prefixEnd_4088346 2099286579886566561173045 := by
  unfold tailWord_4088346
  simp only [CollatzResearch.WordTrace]
  refine ⟨37278557211657037688167223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99409485897752100501779261 37278557211657037688167223)
  ·
    refine ⟨55917835817485556532250835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37278557211657037688167223 55917835817485556532250835)
    ·
      refine ⟨83876753726228334798376253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55917835817485556532250835 83876753726228334798376253)
      ·
        refine ⟨31453782647335625549391095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83876753726228334798376253 31453782647335625549391095)
        ·
          refine ⟨47180673971003438324086643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31453782647335625549391095 47180673971003438324086643)
          ·
            refine ⟨70771010956505157486129965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47180673971003438324086643 70771010956505157486129965)
            ·
              refine ⟨26539129108689434057298737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70771010956505157486129965 26539129108689434057298737)
              ·
                refine ⟨19904346831517075542974053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26539129108689434057298737 19904346831517075542974053)
                ·
                  refine ⟨3732065030909451664307635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19904346831517075542974053 3732065030909451664307635)
                  ·
                    refine ⟨5598097546364177496461453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3732065030909451664307635 5598097546364177496461453)
                    ·
                      refine ⟨2099286579886566561173045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5598097546364177496461453 2099286579886566561173045)
                      ·
                        rfl

theorem cell23_4088346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_4088346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088346 prefixEnd_4088346 := by exact prefixLift 4088346
  have htrace : WordTrace (prefixWord ++ tailWord_4088346) baseStart_4088346 baseEnd_4088346 := by
    simpa [prefixWord, tailWord_4088346, baseEnd_4088346] using wordTrace_append hprefix tailTrace_4088346
  have hstable : (prefixWord ++ tailWord_4088346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088346).length < 2 ^ (prefixWord ++ tailWord_4088346).sum := by decide
  have hdescent : baseEnd_4088346 < baseStart_4088346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088380 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 2, 1, 3]
def baseStart_4088380 : Nat := 118140960795 + 4088380 * 2 ^ 59
def prefixEnd_4088380 : Nat := 4983230072969 + 3 ^ 40 * 4088380 * 2
def baseEnd_4088380 : Nat := 2099304038228819428147889

theorem tailTrace_4088380 : CollatzResearch.WordTrace tailWord_4088380 prefixEnd_4088380 2099304038228819428147889 := by
  unfold tailWord_4088380
  simp only [CollatzResearch.WordTrace]
  refine ⟨74557734464252487279703297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99410312619003316372937729 74557734464252487279703297)
  ·
    refine ⟨55918300848189365459777473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74557734464252487279703297 55918300848189365459777473)
    ·
      refine ⟨41938725636142024094833105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55918300848189365459777473 41938725636142024094833105)
      ·
        refine ⟨31454044227106518071124829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41938725636142024094833105 31454044227106518071124829)
        ·
          refine ⟨11795266585164944276671811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31454044227106518071124829 11795266585164944276671811)
          ·
            refine ⟨17692899877747416415007717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11795266585164944276671811 17692899877747416415007717)
            ·
              refine ⟨3317418727077640577813947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17692899877747416415007717 3317418727077640577813947)
              ·
                refine ⟨4976128090616460866720921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3317418727077640577813947 4976128090616460866720921)
                ·
                  refine ⟨3732096067962345650040691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4976128090616460866720921 3732096067962345650040691)
                  ·
                    refine ⟨5598144101943518475061037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3732096067962345650040691 5598144101943518475061037)
                    ·
                      refine ⟨2099304038228819428147889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5598144101943518475061037 2099304038228819428147889)
                      ·
                        rfl

theorem cell23_4088380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_4088380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088380 prefixEnd_4088380 := by exact prefixLift 4088380
  have htrace : WordTrace (prefixWord ++ tailWord_4088380) baseStart_4088380 baseEnd_4088380 := by
    simpa [prefixWord, tailWord_4088380, baseEnd_4088380] using wordTrace_append hprefix tailTrace_4088380
  have hstable : (prefixWord ++ tailWord_4088380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088380).length < 2 ^ (prefixWord ++ tailWord_4088380).sum := by decide
  have hdescent : baseEnd_4088380 < baseStart_4088380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088389 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_4088389 : Nat := 118140960795 + 4088389 * 2 ^ 59
def prefixEnd_4088389 : Nat := 4983230072969 + 3 ^ 40 * 4088389 * 2
def baseEnd_4088389 : Nat := 2099308659554709892935347

theorem tailTrace_4088389 : CollatzResearch.WordTrace tailWord_4088389 prefixEnd_4088389 2099308659554709892935347 := by
  unfold tailWord_4088389
  simp only [CollatzResearch.WordTrace]
  refine ⟨149115797185472369096484221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99410531456981579397656147 149115797185472369096484221)
  ·
    refine ⟨55918423944552138411181583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149115797185472369096484221 55918423944552138411181583)
    ·
      refine ⟨83877635916828207616772375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55918423944552138411181583 83877635916828207616772375)
      ·
        refine ⟨125816453875242311425158563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83877635916828207616772375 125816453875242311425158563)
        ·
          refine ⟨188724680812863467137737845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125816453875242311425158563 188724680812863467137737845)
          ·
            refine ⟨17692938826205950044162923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188724680812863467137737845 17692938826205950044162923)
            ·
              refine ⟨26539408239308925066244385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17692938826205950044162923 26539408239308925066244385)
              ·
                refine ⟨19904556179481693799683289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26539408239308925066244385 19904556179481693799683289)
                ·
                  refine ⟨14928417134611270349762467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19904556179481693799683289 14928417134611270349762467)
                  ·
                    refine ⟨22392625701916905524643701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14928417134611270349762467 22392625701916905524643701)
                    ·
                      refine ⟨2099308659554709892935347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22392625701916905524643701 2099308659554709892935347)
                      ·
                        rfl

theorem cell23_4088389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_4088389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088389 prefixEnd_4088389 := by exact prefixLift 4088389
  have htrace : WordTrace (prefixWord ++ tailWord_4088389) baseStart_4088389 baseEnd_4088389 := by
    simpa [prefixWord, tailWord_4088389, baseEnd_4088389] using wordTrace_append hprefix tailTrace_4088389
  have hstable : (prefixWord ++ tailWord_4088389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088389).length < 2 ^ (prefixWord ++ tailWord_4088389).sum := by decide
  have hdescent : baseEnd_4088389 < baseStart_4088389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088420 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 2, 2, 2]
def baseStart_4088420 : Nat := 118140960795 + 4088420 * 2 ^ 59
def prefixEnd_4088420 : Nat := 4983230072969 + 3 ^ 40 * 4088420 * 2
def baseEnd_4088420 : Nat := 2099324577454999271647705

theorem tailTrace_4088420 : CollatzResearch.WordTrace tailWord_4088420 prefixEnd_4088420 2099324577454999271647705 := by
  unfold tailWord_4088420
  simp only [CollatzResearch.WordTrace]
  refine ⟨74558463924180030695431357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99411285232240040927241809 74558463924180030695431357)
  ·
    refine ⟨27959423971567511510786759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74558463924180030695431357 27959423971567511510786759)
    ·
      refine ⟨41939135957351267266180139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27959423971567511510786759 41939135957351267266180139)
      ·
        refine ⟨62908703936026900899270209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41939135957351267266180139 62908703936026900899270209)
        ·
          refine ⟨47181527952020175674452657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62908703936026900899270209 47181527952020175674452657)
          ·
            refine ⟨35386145964015131755839493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47181527952020175674452657 35386145964015131755839493)
            ·
              refine ⟨6634902368252837204219905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35386145964015131755839493 6634902368252837204219905)
              ·
                refine ⟨4976176776189627903164929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6634902368252837204219905 4976176776189627903164929)
                ·
                  refine ⟨3732132582142220927373697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4976176776189627903164929 3732132582142220927373697)
                  ·
                    refine ⟨2799099436606665695530273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3732132582142220927373697 2799099436606665695530273)
                    ·
                      refine ⟨2099324577454999271647705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799099436606665695530273 2099324577454999271647705)
                      ·
                        rfl

theorem cell23_4088420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_4088420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088420 prefixEnd_4088420 := by exact prefixLift 4088420
  have htrace : WordTrace (prefixWord ++ tailWord_4088420) baseStart_4088420 baseEnd_4088420 := by
    simpa [prefixWord, tailWord_4088420, baseEnd_4088420] using wordTrace_append hprefix tailTrace_4088420
  have hstable : (prefixWord ++ tailWord_4088420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088420).length < 2 ^ (prefixWord ++ tailWord_4088420).sum := by decide
  have hdescent : baseEnd_4088420 < baseStart_4088420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088439 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 4, 5]
def baseStart_4088439 : Nat := 118140960795 + 4088439 * 2 ^ 59
def prefixEnd_4088439 : Nat := 4983230072969 + 3 ^ 40 * 4088439 * 2
def baseEnd_4088439 : Nat := 699778111195811565770039

theorem tailTrace_4088439 : CollatzResearch.WordTrace tailWord_4088439 prefixEnd_4088439 699778111195811565770039 := by
  unfold tailWord_4088439
  simp only [CollatzResearch.WordTrace]
  refine ⟨149117620835291227635804371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99411747223527485090536247 149117620835291227635804371)
  ·
    refine ⟨223676431252936841453706557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149117620835291227635804371 223676431252936841453706557)
    ·
      refine ⟨83878661719851315545139959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223676431252936841453706557 83878661719851315545139959)
      ·
        refine ⟨125817992579776973317709939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83878661719851315545139959 125817992579776973317709939)
        ·
          refine ⟨188726988869665459976564909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125817992579776973317709939 188726988869665459976564909)
          ·
            refine ⟨70772620826124547491211841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188726988869665459976564909 70772620826124547491211841)
            ·
              refine ⟨53079465619593410618408881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70772620826124547491211841 53079465619593410618408881)
              ·
                refine ⟨39809599214695057963806661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53079465619593410618408881 39809599214695057963806661)
                ·
                  refine ⟨7464299852755323368213749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39809599214695057963806661 7464299852755323368213749)
                  ·
                    refine ⟨699778111195811565770039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7464299852755323368213749 699778111195811565770039)
                    ·
                      rfl

theorem cell23_4088439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_4088439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088439 prefixEnd_4088439 := by exact prefixLift 4088439
  have htrace : WordTrace (prefixWord ++ tailWord_4088439) baseStart_4088439 baseEnd_4088439 := by
    simpa [prefixWord, tailWord_4088439, baseEnd_4088439] using wordTrace_append hprefix tailTrace_4088439
  have hstable : (prefixWord ++ tailWord_4088439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088439).length < 2 ^ (prefixWord ++ tailWord_4088439).sum := by decide
  have hdescent : baseEnd_4088439 < baseStart_4088439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088489 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 4]
def baseStart_4088489 : Nat := 118140960795 + 4088489 * 2 ^ 59
def prefixEnd_4088489 : Nat := 4983230072969 + 3 ^ 40 * 4088489 * 2
def baseEnd_4088489 : Nat := 2099360007620159501684887

theorem tailTrace_4088489 : CollatzResearch.WordTrace tailWord_4088489 prefixEnd_4088489 2099360007620159501684887 := by
  unfold tailWord_4088489
  simp only [CollatzResearch.WordTrace]
  refine ⟨149119444485110086175124521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99412962990073390783416347 149119444485110086175124521)
  ·
    refine ⟨111839583363832564631343391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149119444485110086175124521 111839583363832564631343391)
    ·
      refine ⟨167759375045748846947015087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111839583363832564631343391 167759375045748846947015087)
      ·
        refine ⟨251639062568623270420522631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167759375045748846947015087 251639062568623270420522631)
        ·
          refine ⟨377458593852934905630783947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251639062568623270420522631 377458593852934905630783947)
          ·
            refine ⟨566187890779402358446175921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377458593852934905630783947 566187890779402358446175921)
            ·
              refine ⟨424640918084551768834631941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566187890779402358446175921 424640918084551768834631941)
              ·
                refine ⟨79620172140853456656493489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 424640918084551768834631941 79620172140853456656493489)
                ·
                  refine ⟨59715129105640092492370117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79620172140853456656493489 59715129105640092492370117)
                  ·
                    refine ⟨11196586707307517342319397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59715129105640092492370117 11196586707307517342319397)
                    ·
                      refine ⟨2099360007620159501684887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11196586707307517342319397 2099360007620159501684887)
                      ·
                        rfl

theorem cell23_4088489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_4088489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088489 prefixEnd_4088489 := by exact prefixLift 4088489
  have htrace : WordTrace (prefixWord ++ tailWord_4088489) baseStart_4088489 baseEnd_4088489 := by
    simpa [prefixWord, tailWord_4088489, baseEnd_4088489] using wordTrace_append hprefix tailTrace_4088489
  have hstable : (prefixWord ++ tailWord_4088489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088489).length < 2 ^ (prefixWord ++ tailWord_4088489).sum := by decide
  have hdescent : baseEnd_4088489 < baseStart_4088489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088516 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 8]
def baseStart_4088516 : Nat := 118140960795 + 4088516 * 2 ^ 59
def prefixEnd_4088516 : Nat := 4983230072969 + 3 ^ 40 * 4088516 * 2
def baseEnd_4088516 : Nat := 233263763510870099560807

theorem tailTrace_4088516 : CollatzResearch.WordTrace tailWord_4088516 prefixEnd_4088516 233263763510870099560807 := by
  unfold tailWord_4088516
  simp only [CollatzResearch.WordTrace]
  refine ⟨74560214628006134893178701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99413619504008179857571601 74560214628006134893178701)
  ·
    refine ⟨27960080485502300584942013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74560214628006134893178701 27960080485502300584942013)
    ·
      refine ⟨10485030182063362719353255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27960080485502300584942013 10485030182063362719353255)
      ·
        refine ⟨15727545273095044079029883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10485030182063362719353255 15727545273095044079029883)
        ·
          refine ⟨23591317909642566118544825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15727545273095044079029883 23591317909642566118544825)
          ·
            refine ⟨17693488432231924588908619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23591317909642566118544825 17693488432231924588908619)
            ·
              refine ⟨26540232648347886883362929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17693488432231924588908619 26540232648347886883362929)
              ·
                refine ⟨19905174486260915162522197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26540232648347886883362929 19905174486260915162522197)
                ·
                  refine ⟨233263763510870099560807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19905174486260915162522197 233263763510870099560807)
                  ·
                    rfl

theorem cell23_4088516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_4088516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088516 prefixEnd_4088516 := by exact prefixLift 4088516
  have htrace : WordTrace (prefixWord ++ tailWord_4088516) baseStart_4088516 baseEnd_4088516 := by
    simpa [prefixWord, tailWord_4088516, baseEnd_4088516] using wordTrace_append hprefix tailTrace_4088516
  have hstable : (prefixWord ++ tailWord_4088516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088516).length < 2 ^ (prefixWord ++ tailWord_4088516).sum := by decide
  have hdescent : baseEnd_4088516 < baseStart_4088516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088519 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_4088519 : Nat := 118140960795 + 4088519 * 2 ^ 59
def prefixEnd_4088519 : Nat := 4983230072969 + 3 ^ 40 * 4088519 * 2
def baseEnd_4088519 : Nat := 2099375412039794384309749

theorem tailTrace_4088519 : CollatzResearch.WordTrace tailWord_4088519 prefixEnd_4088519 2099375412039794384309749 := by
  unfold tailWord_4088519
  simp only [CollatzResearch.WordTrace]
  refine ⟨149120538675001401298716611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99413692450000934199144407 149120538675001401298716611)
  ·
    refine ⟨223680808012502101948074917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149120538675001401298716611 223680808012502101948074917)
    ·
      refine ⟨41940151502344144115264047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223680808012502101948074917 41940151502344144115264047)
      ·
        refine ⟨62910227253516216172896071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41940151502344144115264047 62910227253516216172896071)
        ·
          refine ⟨94365340880274324259344107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62910227253516216172896071 94365340880274324259344107)
          ·
            refine ⟨141548011320411486389016161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94365340880274324259344107 141548011320411486389016161)
            ·
              refine ⟨106161008490308614791762121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141548011320411486389016161 106161008490308614791762121)
              ·
                refine ⟨79620756367731461093821591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106161008490308614791762121 79620756367731461093821591)
                ·
                  refine ⟨119431134551597191640732387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79620756367731461093821591 119431134551597191640732387)
                  ·
                    refine ⟨179146701827395787461098581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119431134551597191640732387 179146701827395787461098581)
                    ·
                      refine ⟨2099375412039794384309749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 179146701827395787461098581 2099375412039794384309749)
                      ·
                        rfl

theorem cell23_4088519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_4088519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088519 prefixEnd_4088519 := by exact prefixLift 4088519
  have htrace : WordTrace (prefixWord ++ tailWord_4088519) baseStart_4088519 baseEnd_4088519 := by
    simpa [prefixWord, tailWord_4088519, baseEnd_4088519] using wordTrace_append hprefix tailTrace_4088519
  have hstable : (prefixWord ++ tailWord_4088519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088519).length < 2 ^ (prefixWord ++ tailWord_4088519).sum := by decide
  have hdescent : baseEnd_4088519 < baseStart_4088519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088520 : List Nat := [2, 1, 3, 1, 2, 3, 3, 3, 1, 4]
def baseStart_4088520 : Nat := 118140960795 + 4088520 * 2 ^ 59
def prefixEnd_4088520 : Nat := 4983230072969 + 3 ^ 40 * 4088520 * 2
def baseEnd_4088520 : Nat := 699791975173482960132415

theorem tailTrace_4088520 : CollatzResearch.WordTrace tailWord_4088520 prefixEnd_4088520 699791975173482960132415 := by
  unfold tailWord_4088520
  simp only [CollatzResearch.WordTrace]
  refine ⟨74560287573998889234751507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99413716765331852313002009 74560287573998889234751507)
  ·
    refine ⟨111840431360998333852127261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74560287573998889234751507 111840431360998333852127261)
    ·
      refine ⟨41940161760374375194547723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111840431360998333852127261 41940161760374375194547723)
      ·
        refine ⟨62910242640561562791821585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41940161760374375194547723 62910242640561562791821585)
        ·
          refine ⟨47182681980421172093866189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62910242640561562791821585 47182681980421172093866189)
          ·
            refine ⟨17693505742657939535199821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47182681980421172093866189 17693505742657939535199821)
            ·
              refine ⟨6635064653496727325699933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17693505742657939535199821 6635064653496727325699933)
              ·
                refine ⟨2488149245061272747137475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6635064653496727325699933 2488149245061272747137475)
                ·
                  refine ⟨3732223867591909120706213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488149245061272747137475 3732223867591909120706213)
                  ·
                    refine ⟨699791975173482960132415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3732223867591909120706213 699791975173482960132415)
                    ·
                      rfl

theorem cell23_4088520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_4088520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088520 prefixEnd_4088520 := by exact prefixLift 4088520
  have htrace : WordTrace (prefixWord ++ tailWord_4088520) baseStart_4088520 baseEnd_4088520 := by
    simpa [prefixWord, tailWord_4088520, baseEnd_4088520] using wordTrace_append hprefix tailTrace_4088520
  have hstable : (prefixWord ++ tailWord_4088520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088520).length < 2 ^ (prefixWord ++ tailWord_4088520).sum := by decide
  have hdescent : baseEnd_4088520 < baseStart_4088520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088530 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_4088530 : Nat := 118140960795 + 4088530 * 2 ^ 59
def prefixEnd_4088530 : Nat := 4983230072969 + 3 ^ 40 * 4088530 * 2
def baseEnd_4088530 : Nat := 2099381060326993841272199

theorem tailTrace_4088530 : CollatzResearch.WordTrace tailWord_4088530 prefixEnd_4088530 2099381060326993841272199 := by
  unfold tailWord_4088530
  simp only [CollatzResearch.WordTrace]
  refine ⟨37280234969490387544341761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99413959918641033451578029 37280234969490387544341761)
  ·
    refine ⟨27960176227117790658256321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37280234969490387544341761 27960176227117790658256321)
    ·
      refine ⟨20970132170338342993692241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27960176227117790658256321 20970132170338342993692241)
      ·
        refine ⟨15727599127753757245269181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20970132170338342993692241 15727599127753757245269181)
        ·
          refine ⟨5897849672907658966975943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15727599127753757245269181 5897849672907658966975943)
          ·
            refine ⟨8846774509361488450463915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5897849672907658966975943 8846774509361488450463915)
            ·
              refine ⟨13270161764042232675695873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8846774509361488450463915 13270161764042232675695873)
              ·
                refine ⟨9952621323031674506771905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13270161764042232675695873 9952621323031674506771905)
                ·
                  refine ⟨7464465992273755880078929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9952621323031674506771905 7464465992273755880078929)
                  ·
                    refine ⟨5598349494205316910059197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7464465992273755880078929 5598349494205316910059197)
                    ·
                      refine ⟨2099381060326993841272199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5598349494205316910059197 2099381060326993841272199)
                      ·
                        rfl

theorem cell23_4088530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_4088530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088530 prefixEnd_4088530 := by exact prefixLift 4088530
  have htrace : WordTrace (prefixWord ++ tailWord_4088530) baseStart_4088530 baseEnd_4088530 := by
    simpa [prefixWord, tailWord_4088530, baseEnd_4088530] using wordTrace_append hprefix tailTrace_4088530
  have hstable : (prefixWord ++ tailWord_4088530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088530).length < 2 ^ (prefixWord ++ tailWord_4088530).sum := by decide
  have hdescent : baseEnd_4088530 < baseStart_4088530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088539 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 5]
def baseStart_4088539 : Nat := 118140960795 + 4088539 * 2 ^ 59
def prefixEnd_4088539 : Nat := 4983230072969 + 3 ^ 40 * 4088539 * 2
def baseEnd_4088539 : Nat := 2099385681652884306059657

theorem tailTrace_4088539 : CollatzResearch.WordTrace tailWord_4088539 prefixEnd_4088539 2099385681652884306059657 := by
  unfold tailWord_4088539
  simp only [CollatzResearch.WordTrace]
  refine ⟨149121268134928944714444671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99414178756619296476296447 149121268134928944714444671)
  ·
    refine ⟨223681902202393417071667007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149121268134928944714444671 223681902202393417071667007)
    ·
      refine ⟨335522853303590125607500511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223681902202393417071667007 335522853303590125607500511)
      ·
        refine ⟨503284279955385188411250767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335522853303590125607500511 503284279955385188411250767)
        ·
          refine ⟨754926419933077782616876151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503284279955385188411250767 754926419933077782616876151)
          ·
            refine ⟨1132389629899616673925314227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754926419933077782616876151 1132389629899616673925314227)
            ·
              refine ⟨1698584444849425010887971341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132389629899616673925314227 1698584444849425010887971341)
              ·
                refine ⟨636969166818534379082989253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1698584444849425010887971341 636969166818534379082989253)
                ·
                  refine ⟨119431718778475196078060485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636969166818534379082989253 119431718778475196078060485)
                  ·
                    refine ⟨22393447270964099264636341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119431718778475196078060485 22393447270964099264636341)
                    ·
                      refine ⟨2099385681652884306059657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22393447270964099264636341 2099385681652884306059657)
                      ·
                        rfl

theorem cell23_4088539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_4088539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088539 prefixEnd_4088539 := by exact prefixLift 4088539
  have htrace : WordTrace (prefixWord ++ tailWord_4088539) baseStart_4088539 baseEnd_4088539 := by
    simpa [prefixWord, tailWord_4088539, baseEnd_4088539] using wordTrace_append hprefix tailTrace_4088539
  have hstable : (prefixWord ++ tailWord_4088539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088539).length < 2 ^ (prefixWord ++ tailWord_4088539).sum := by decide
  have hdescent : baseEnd_4088539 < baseStart_4088539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088564 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_4088564 : Nat := 118140960795 + 4088564 * 2 ^ 59
def prefixEnd_4088564 : Nat := 4983230072969 + 3 ^ 40 * 4088564 * 2
def baseEnd_4088564 : Nat := 2099398518669246708247043

theorem tailTrace_4088564 : CollatzResearch.WordTrace tailWord_4088564 prefixEnd_4088564 2099398518669246708247043 := by
  unfold tailWord_4088564
  simp only [CollatzResearch.WordTrace]
  refine ⟨74561089979919186992052373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99414786639892249322736497 74561089979919186992052373)
  ·
    refine ⟨3495051092808711890252455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74561089979919186992052373 3495051092808711890252455)
    ·
      refine ⟨5242576639213067835378683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3495051092808711890252455 5242576639213067835378683)
      ·
        refine ⟨7863864958819601753068025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5242576639213067835378683 7863864958819601753068025)
        ·
          refine ⟨5897898719114701314801019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7863864958819601753068025 5897898719114701314801019)
          ·
            refine ⟨8846848078672051972201529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5897898719114701314801019 8846848078672051972201529)
            ·
              refine ⟨6635136059004038979151147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8846848078672051972201529 6635136059004038979151147)
              ·
                refine ⟨9952704088506058468726721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6635136059004038979151147 9952704088506058468726721)
                ·
                  refine ⟨7464528066379543851545041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9952704088506058468726721 7464528066379543851545041)
                  ·
                    refine ⟨5598396049784657888658781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7464528066379543851545041 5598396049784657888658781)
                    ·
                      refine ⟨2099398518669246708247043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5598396049784657888658781 2099398518669246708247043)
                      ·
                        rfl

theorem cell23_4088564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_4088564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088564 prefixEnd_4088564 := by exact prefixLift 4088564
  have htrace : WordTrace (prefixWord ++ tailWord_4088564) baseStart_4088564 baseEnd_4088564 := by
    simpa [prefixWord, tailWord_4088564, baseEnd_4088564] using wordTrace_append hprefix tailTrace_4088564
  have hstable : (prefixWord ++ tailWord_4088564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088564).length < 2 ^ (prefixWord ++ tailWord_4088564).sum := by decide
  have hdescent : baseEnd_4088564 < baseStart_4088564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088580 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_4088580 : Nat := 118140960795 + 4088580 * 2 ^ 59
def prefixEnd_4088580 : Nat := 4983230072969 + 3 ^ 40 * 4088580 * 2
def baseEnd_4088580 : Nat := 699802244786572881882323

theorem tailTrace_4088580 : CollatzResearch.WordTrace tailWord_4088580 prefixEnd_4088580 699802244786572881882323 := by
  unfold tailWord_4088580
  simp only [CollatzResearch.WordTrace]
  refine ⟨74561381763890204358343597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99415175685186939144458129 74561381763890204358343597)
  ·
    refine ⟨27960518161458826634378849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74561381763890204358343597 27960518161458826634378849)
    ·
      refine ⟨20970388621094119975784137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27960518161458826634378849 20970388621094119975784137)
      ·
        refine ⟨15727791465820589981838103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20970388621094119975784137 15727791465820589981838103)
        ·
          refine ⟨23591687198730884972757155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15727791465820589981838103 23591687198730884972757155)
          ·
            refine ⟨35387530798096327459135733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23591687198730884972757155 35387530798096327459135733)
            ·
              refine ⟨3317581012321530699293975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35387530798096327459135733 3317581012321530699293975)
              ·
                refine ⟨4976371518482296048940963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3317581012321530699293975 4976371518482296048940963)
                ·
                  refine ⟨7464557277723444073411445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976371518482296048940963 7464557277723444073411445)
                  ·
                    refine ⟨699802244786572881882323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7464557277723444073411445 699802244786572881882323)
                    ·
                      rfl

theorem cell23_4088580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_4088580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088580 prefixEnd_4088580 := by exact prefixLift 4088580
  have htrace : WordTrace (prefixWord ++ tailWord_4088580) baseStart_4088580 baseEnd_4088580 := by
    simpa [prefixWord, tailWord_4088580, baseEnd_4088580] using wordTrace_append hprefix tailTrace_4088580
  have hstable : (prefixWord ++ tailWord_4088580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088580).length < 2 ^ (prefixWord ++ tailWord_4088580).sum := by decide
  have hdescent : baseEnd_4088580 < baseStart_4088580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088593 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 2, 4]
def baseStart_4088593 : Nat := 118140960795 + 4088593 * 2 ^ 59
def prefixEnd_4088593 : Nat := 4983230072969 + 3 ^ 40 * 4088593 * 2
def baseEnd_4088593 : Nat := 699804469869409031594803

theorem tailTrace_4088593 : CollatzResearch.WordTrace tailWord_4088593 prefixEnd_4088593 699804469869409031594803 := by
  unfold tailWord_4088593
  simp only [CollatzResearch.WordTrace]
  refine ⟨149123237676733311936910433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99415491784488874624606955 149123237676733311936910433)
  ·
    refine ⟨111842428257549983952682825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149123237676733311936910433 111842428257549983952682825)
    ·
      refine ⟨83881821193162487964512119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111842428257549983952682825 83881821193162487964512119)
      ·
        refine ⟨125822731789743731946768179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83881821193162487964512119 125822731789743731946768179)
        ·
          refine ⟨188734097684615597920152269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125822731789743731946768179 188734097684615597920152269)
          ·
            refine ⟨70775286631730849220057101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188734097684615597920152269 70775286631730849220057101)
            ·
              refine ⟨26540732486899068457521413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70775286631730849220057101 26540732486899068457521413)
              ·
                refine ⟨4976387341293575335785265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26540732486899068457521413 4976387341293575335785265)
                ·
                  refine ⟨3732290505970181501838949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4976387341293575335785265 3732290505970181501838949)
                  ·
                    refine ⟨699804469869409031594803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3732290505970181501838949 699804469869409031594803)
                    ·
                      rfl

theorem cell23_4088593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_4088593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088593 prefixEnd_4088593 := by exact prefixLift 4088593
  have htrace : WordTrace (prefixWord ++ tailWord_4088593) baseStart_4088593 baseEnd_4088593 := by
    simpa [prefixWord, tailWord_4088593, baseEnd_4088593] using wordTrace_append hprefix tailTrace_4088593
  have hstable : (prefixWord ++ tailWord_4088593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088593).length < 2 ^ (prefixWord ++ tailWord_4088593).sum := by decide
  have hdescent : baseEnd_4088593 < baseStart_4088593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088600 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 3, 2, 2]
def baseStart_4088600 : Nat := 118140960795 + 4088600 * 2 ^ 59
def prefixEnd_4088600 : Nat := 4983230072969 + 3 ^ 40 * 4088600 * 2
def baseEnd_4088600 : Nat := 2099417003972808567396877

theorem tailTrace_4088600 : CollatzResearch.WordTrace tailWord_4088600 prefixEnd_4088600 2099417003972808567396877 := by
  unfold tailWord_4088600
  simp only [CollatzResearch.WordTrace]
  refine ⟨74561746493853976066207627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99415661991805301421610169 74561746493853976066207627)
  ·
    refine ⟨111842619740780964099311441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74561746493853976066207627 111842619740780964099311441)
    ·
      refine ⟨83881964805585723074483581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111842619740780964099311441 83881964805585723074483581)
      ·
        refine ⟨31455736802094646152931343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83881964805585723074483581 31455736802094646152931343)
        ·
          refine ⟨47183605203141969229397015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31455736802094646152931343 47183605203141969229397015)
          ·
            refine ⟨70775407804712953844095523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47183605203141969229397015 70775407804712953844095523)
            ·
              refine ⟨106163111707069430766143285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70775407804712953844095523 106163111707069430766143285)
              ·
                refine ⟨9952791722537759134325933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106163111707069430766143285 9952791722537759134325933)
                ·
                  refine ⟨3732296895951659675372225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9952791722537759134325933 3732296895951659675372225)
                  ·
                    refine ⟨2799222671963744756529169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3732296895951659675372225 2799222671963744756529169)
                    ·
                      refine ⟨2099417003972808567396877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799222671963744756529169 2099417003972808567396877)
                      ·
                        rfl

theorem cell23_4088600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_4088600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088600 prefixEnd_4088600 := by exact prefixLift 4088600
  have htrace : WordTrace (prefixWord ++ tailWord_4088600) baseStart_4088600 baseEnd_4088600 := by
    simpa [prefixWord, tailWord_4088600, baseEnd_4088600] using wordTrace_append hprefix tailTrace_4088600
  have hstable : (prefixWord ++ tailWord_4088600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088600).length < 2 ^ (prefixWord ++ tailWord_4088600).sum := by decide
  have hdescent : baseEnd_4088600 < baseStart_4088600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088610 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_4088610 : Nat := 118140960795 + 4088610 * 2 ^ 59
def prefixEnd_4088610 : Nat := 4983230072969 + 3 ^ 40 * 4088610 * 2
def baseEnd_4088610 : Nat := 699807379593117842757277

theorem tailTrace_4088610 : CollatzResearch.WordTrace tailWord_4088610 prefixEnd_4088610 699807379593117842757277 := by
  unfold tailWord_4088610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37280964429417930960069821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99415905145114482560186189 37280964429417930960069821)
  ·
    refine ⟨13980361661031724110026183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37280964429417930960069821 13980361661031724110026183)
    ·
      refine ⟨20970542491547586165039275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13980361661031724110026183 20970542491547586165039275)
      ·
        refine ⟨31455813737321379247558913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20970542491547586165039275 31455813737321379247558913)
        ·
          refine ⟨23591860302991034435669185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31455813737321379247558913 23591860302991034435669185)
          ·
            refine ⟨17693895227243275826751889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23591860302991034435669185 17693895227243275826751889)
            ·
              refine ⟨13270421420432456870063917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17693895227243275826751889 13270421420432456870063917)
              ·
                refine ⟨4976408032662171326273969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13270421420432456870063917 4976408032662171326273969)
                ·
                  refine ⟨3732306024496628494705477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4976408032662171326273969 3732306024496628494705477)
                  ·
                    refine ⟨699807379593117842757277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3732306024496628494705477 699807379593117842757277)
                    ·
                      rfl

theorem cell23_4088610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_4088610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088610 prefixEnd_4088610 := by exact prefixLift 4088610
  have htrace : WordTrace (prefixWord ++ tailWord_4088610) baseStart_4088610 baseEnd_4088610 := by
    simpa [prefixWord, tailWord_4088610, baseEnd_4088610] using wordTrace_append hprefix tailTrace_4088610
  have hstable : (prefixWord ++ tailWord_4088610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088610).length < 2 ^ (prefixWord ++ tailWord_4088610).sum := by decide
  have hdescent : baseEnd_4088610 < baseStart_4088610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088613 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 4]
def baseStart_4088613 : Nat := 118140960795 + 4088613 * 2 ^ 59
def prefixEnd_4088613 : Nat := 4983230072969 + 3 ^ 40 * 4088613 * 2
def baseEnd_4088613 : Nat := 2099423679221317016534317

theorem tailTrace_4088613 : CollatzResearch.WordTrace tailWord_4088613 prefixEnd_4088613 2099423679221317016534317 := by
  unfold tailWord_4088613
  simp only [CollatzResearch.WordTrace]
  refine ⟨149123967136660855352638493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99415978091107236901758995 149123967136660855352638493)
  ·
    refine ⟨55921487676247820757239435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149123967136660855352638493 55921487676247820757239435)
    ·
      refine ⟨83882231514371731135859153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55921487676247820757239435 83882231514371731135859153)
      ·
        refine ⟨62911673635778798351894365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83882231514371731135859153 62911673635778798351894365)
        ·
          refine ⟨23591877613417049381960387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62911673635778798351894365 23591877613417049381960387)
          ·
            refine ⟨35387816420125574072940581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23591877613417049381960387 35387816420125574072940581)
            ·
              refine ⟨6635215578773545138676359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35387816420125574072940581 6635215578773545138676359)
              ·
                refine ⟨9952823368160317708014539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6635215578773545138676359 9952823368160317708014539)
                ·
                  refine ⟨14929235052240476562021809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9952823368160317708014539 14929235052240476562021809)
                  ·
                    refine ⟨11196926289180357421516357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14929235052240476562021809 11196926289180357421516357)
                    ·
                      refine ⟨2099423679221317016534317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11196926289180357421516357 2099423679221317016534317)
                      ·
                        rfl

theorem cell23_4088613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_4088613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088613 prefixEnd_4088613 := by exact prefixLift 4088613
  have htrace : WordTrace (prefixWord ++ tailWord_4088613) baseStart_4088613 baseEnd_4088613 := by
    simpa [prefixWord, tailWord_4088613, baseEnd_4088613] using wordTrace_append hprefix tailTrace_4088613
  have hstable : (prefixWord ++ tailWord_4088613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088613).length < 2 ^ (prefixWord ++ tailWord_4088613).sum := by decide
  have hdescent : baseEnd_4088613 < baseStart_4088613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088621 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4088621 : Nat := 118140960795 + 4088621 * 2 ^ 59
def prefixEnd_4088621 : Nat := 4983230072969 + 3 ^ 40 * 4088621 * 2
def baseEnd_4088621 : Nat := 2099427787066552985234281

theorem tailTrace_4088621 : CollatzResearch.WordTrace tailWord_4088621 prefixEnd_4088621 2099427787066552985234281 := by
  unfold tailWord_4088621
  simp only [CollatzResearch.WordTrace]
  refine ⟨149124258920631872718929717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99416172613754581812619811 149124258920631872718929717)
  ·
    refine ⟨13980399273809238067399661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149124258920631872718929717 13980399273809238067399661)
    ·
      refine ⟨5242649727678464275274873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13980399273809238067399661 5242649727678464275274873)
      ·
        refine ⟨3931987295758848206456155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5242649727678464275274873 3931987295758848206456155)
        ·
          refine ⟨5897980943638272309684233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931987295758848206456155 5897980943638272309684233)
          ·
            refine ⟨4423485707728704232263175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5897980943638272309684233 4423485707728704232263175)
            ·
              refine ⟨6635228561593056348394763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423485707728704232263175 6635228561593056348394763)
              ·
                refine ⟨9952842842389584522592145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6635228561593056348394763 9952842842389584522592145)
                ·
                  refine ⟨7464632131792188391944109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9952842842389584522592145 7464632131792188391944109)
                  ·
                    refine ⟨2799237049422070646979041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7464632131792188391944109 2799237049422070646979041)
                    ·
                      refine ⟨2099427787066552985234281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799237049422070646979041 2099427787066552985234281)
                      ·
                        rfl

theorem cell23_4088621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4088621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088621 prefixEnd_4088621 := by exact prefixLift 4088621
  have htrace : WordTrace (prefixWord ++ tailWord_4088621) baseStart_4088621 baseEnd_4088621 := by
    simpa [prefixWord, tailWord_4088621, baseEnd_4088621] using wordTrace_append hprefix tailTrace_4088621
  have hstable : (prefixWord ++ tailWord_4088621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088621).length < 2 ^ (prefixWord ++ tailWord_4088621).sum := by decide
  have hdescent : baseEnd_4088621 < baseStart_4088621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088634 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4]
def baseStart_4088634 : Nat := 118140960795 + 4088634 * 2 ^ 59
def prefixEnd_4088634 : Nat := 4983230072969 + 3 ^ 40 * 4088634 * 2
def baseEnd_4088634 : Nat := 2099434462315061434371721

theorem tailTrace_4088634 : CollatzResearch.WordTrace tailWord_4088634 prefixEnd_4088634 2099434462315061434371721 := by
  unfold tailWord_4088634
  simp only [CollatzResearch.WordTrace]
  refine ⟨37281183267396193984788239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99416488713056517292768637 37281183267396193984788239)
  ·
    refine ⟨55921774901094290977182359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37281183267396193984788239 55921774901094290977182359)
    ·
      refine ⟨83882662351641436465773539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55921774901094290977182359 83882662351641436465773539)
      ·
        refine ⟨125823993527462154698660309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83882662351641436465773539 125823993527462154698660309)
        ·
          refine ⟨2948999848299894250749851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 125823993527462154698660309 2948999848299894250749851)
          ·
            refine ⟨4423499772449841376124777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948999848299894250749851 4423499772449841376124777)
            ·
              refine ⟨3317624829337381032093583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4423499772449841376124777 3317624829337381032093583)
              ·
                refine ⟨4976437244006071548140375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3317624829337381032093583 4976437244006071548140375)
                ·
                  refine ⟨7464655866009107322210563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976437244006071548140375 7464655866009107322210563)
                  ·
                    refine ⟨11196983799013660983315845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464655866009107322210563 11196983799013660983315845)
                    ·
                      refine ⟨2099434462315061434371721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11196983799013660983315845 2099434462315061434371721)
                      ·
                        rfl

theorem cell23_4088634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4].length) (baseStart_4088634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088634 prefixEnd_4088634 := by exact prefixLift 4088634
  have htrace : WordTrace (prefixWord ++ tailWord_4088634) baseStart_4088634 baseEnd_4088634 := by
    simpa [prefixWord, tailWord_4088634, baseEnd_4088634] using wordTrace_append hprefix tailTrace_4088634
  have hstable : (prefixWord ++ tailWord_4088634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088634).length < 2 ^ (prefixWord ++ tailWord_4088634).sum := by decide
  have hdescent : baseEnd_4088634 < baseStart_4088634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088637 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_4088637 : Nat := 118140960795 + 4088637 * 2 ^ 59
def prefixEnd_4088637 : Nat := 4983230072969 + 3 ^ 40 * 4088637 * 2
def baseEnd_4088637 : Nat := 2099436002757024922634207

theorem tailTrace_4088637 : CollatzResearch.WordTrace tailWord_4088637 prefixEnd_4088637 2099436002757024922634207 := by
  unfold tailWord_4088637
  simp only [CollatzResearch.WordTrace]
  refine ⟨149124842488573907451512165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99416561659049271634341443 149124842488573907451512165)
  ·
    refine ⟨27960907966607607647158531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149124842488573907451512165 27960907966607607647158531)
    ·
      refine ⟨41941361949911411470737797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27960907966607607647158531 41941361949911411470737797)
      ·
        refine ⟨7864005365608389650763337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41941361949911411470737797 7864005365608389650763337)
        ·
          refine ⟨5898004024206292238072503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7864005365608389650763337 5898004024206292238072503)
          ·
            refine ⟨8847006036309438357108755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5898004024206292238072503 8847006036309438357108755)
            ·
              refine ⟨13270509054464157535663133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8847006036309438357108755 13270509054464157535663133)
              ·
                refine ⟨4976440895424059075873675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13270509054464157535663133 4976440895424059075873675)
                ·
                  refine ⟨7464661343136088613810513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976440895424059075873675 7464661343136088613810513)
                  ·
                    refine ⟨5598496007352066460357885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7464661343136088613810513 5598496007352066460357885)
                    ·
                      refine ⟨2099436002757024922634207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5598496007352066460357885 2099436002757024922634207)
                      ·
                        rfl

theorem cell23_4088637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_4088637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088637 prefixEnd_4088637 := by exact prefixLift 4088637
  have htrace : WordTrace (prefixWord ++ tailWord_4088637) baseStart_4088637 baseEnd_4088637 := by
    simpa [prefixWord, tailWord_4088637, baseEnd_4088637] using wordTrace_append hprefix tailTrace_4088637
  have hstable : (prefixWord ++ tailWord_4088637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088637).length < 2 ^ (prefixWord ++ tailWord_4088637).sum := by decide
  have hdescent : baseEnd_4088637 < baseStart_4088637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088650 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_4088650 : Nat := 118140960795 + 4088650 * 2 ^ 59
def prefixEnd_4088650 : Nat := 4983230072969 + 3 ^ 40 * 4088650 * 2
def baseEnd_4088650 : Nat := 2099442678005533371771647

theorem tailTrace_4088650 : CollatzResearch.WordTrace tailWord_4088650 prefixEnd_4088650 2099442678005533371771647 := by
  unfold tailWord_4088650
  simp only [CollatzResearch.WordTrace]
  refine ⟨37281329159381702667933851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99416877758351207114490269 37281329159381702667933851)
  ·
    refine ⟨55921993739072554001900777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37281329159381702667933851 55921993739072554001900777)
    ·
      refine ⟨41941495304304415501425583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55921993739072554001900777 41941495304304415501425583)
      ·
        refine ⟨62912242956456623252138375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41941495304304415501425583 62912242956456623252138375)
        ·
          refine ⟨94368364434684934878207563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62912242956456623252138375 94368364434684934878207563)
          ·
            refine ⟨141552546652027402317311345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94368364434684934878207563 141552546652027402317311345)
            ·
              refine ⟨106164409989020551737983509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141552546652027402317311345 106164409989020551737983509)
              ·
                refine ⟨4976456718235338362717977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106164409989020551737983509 4976456718235338362717977)
                ·
                  refine ⟨3732342538676503772038483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4976456718235338362717977 3732342538676503772038483)
                  ·
                    refine ⟨5598513808014755658057725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3732342538676503772038483 5598513808014755658057725)
                    ·
                      refine ⟨2099442678005533371771647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5598513808014755658057725 2099442678005533371771647)
                      ·
                        rfl

theorem cell23_4088650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_4088650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088650 prefixEnd_4088650 := by exact prefixLift 4088650
  have htrace : WordTrace (prefixWord ++ tailWord_4088650) baseStart_4088650 baseEnd_4088650 := by
    simpa [prefixWord, tailWord_4088650, baseEnd_4088650] using wordTrace_append hprefix tailTrace_4088650
  have hstable : (prefixWord ++ tailWord_4088650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088650).length < 2 ^ (prefixWord ++ tailWord_4088650).sum := by decide
  have hdescent : baseEnd_4088650 < baseStart_4088650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088656 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 4]
def baseStart_4088656 : Nat := 118140960795 + 4088656 * 2 ^ 59
def prefixEnd_4088656 : Nat := 4983230072969 + 3 ^ 40 * 4088656 * 2
def baseEnd_4088656 : Nat := 2099445758889460348296619

theorem tailTrace_4088656 : CollatzResearch.WordTrace tailWord_4088656 prefixEnd_4088656 2099445758889460348296619 := by
  unfold tailWord_4088656
  simp only [CollatzResearch.WordTrace]
  refine ⟨74562767737752536848226911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99417023650336715797635881 74562767737752536848226911)
  ·
    refine ⟨111844151606628805272340367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74562767737752536848226911 111844151606628805272340367)
    ·
      refine ⟨167766227409943207908510551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111844151606628805272340367 167766227409943207908510551)
      ·
        refine ⟨251649341114914811862765827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167766227409943207908510551 251649341114914811862765827)
        ·
          refine ⟨377474011672372217794148741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251649341114914811862765827 377474011672372217794148741)
          ·
            refine ⟨70776377188569790836402889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377474011672372217794148741 70776377188569790836402889)
            ·
              refine ⟨53082282891427343127302167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70776377188569790836402889 53082282891427343127302167)
              ·
                refine ⟨79623424337141014690953251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53082282891427343127302167 79623424337141014690953251)
                ·
                  refine ⟨119435136505711522036429877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79623424337141014690953251 119435136505711522036429877)
                  ·
                    refine ⟨11197044047410455190915301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119435136505711522036429877 11197044047410455190915301)
                    ·
                      refine ⟨2099445758889460348296619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11197044047410455190915301 2099445758889460348296619)
                      ·
                        rfl

theorem cell23_4088656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_4088656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088656 prefixEnd_4088656 := by exact prefixLift 4088656
  have htrace : WordTrace (prefixWord ++ tailWord_4088656) baseStart_4088656 baseEnd_4088656 := by
    simpa [prefixWord, tailWord_4088656, baseEnd_4088656] using wordTrace_append hprefix tailTrace_4088656
  have hstable : (prefixWord ++ tailWord_4088656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088656).length < 2 ^ (prefixWord ++ tailWord_4088656).sum := by decide
  have hdescent : baseEnd_4088656 < baseStart_4088656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088690 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 1, 4, 2]
def baseStart_4088690 : Nat := 118140960795 + 4088690 * 2 ^ 59
def prefixEnd_4088690 : Nat := 4983230072969 + 3 ^ 40 * 4088690 * 2
def baseEnd_4088690 : Nat := 2099463217231713215271463

theorem tailTrace_4088690 : CollatzResearch.WordTrace tailWord_4088690 prefixEnd_4088690 2099463217231713215271463 := by
  unfold tailWord_4088690
  simp only [CollatzResearch.WordTrace]
  refine ⟨37281693889345474375797881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99417850371587931668794349 37281693889345474375797881)
  ·
    refine ⟨27961270417009105781848411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37281693889345474375797881 27961270417009105781848411)
    ·
      refine ⟨41941905625513658672772617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27961270417009105781848411 41941905625513658672772617)
      ·
        refine ⟨31456429219135244004579463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41941905625513658672772617 31456429219135244004579463)
        ·
          refine ⟨47184643828702866006869195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31456429219135244004579463 47184643828702866006869195)
          ·
            refine ⟨70776965743054299010303793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47184643828702866006869195 70776965743054299010303793)
            ·
              refine ⟨53082724307290724257727845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70776965743054299010303793 53082724307290724257727845)
              ·
                refine ⟨9953010807617010798323971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53082724307290724257727845 9953010807617010798323971)
                ·
                  refine ⟨14929516211425516197485957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9953010807617010798323971 14929516211425516197485957)
                  ·
                    refine ⟨2799284289642284287028617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14929516211425516197485957 2799284289642284287028617)
                    ·
                      refine ⟨2099463217231713215271463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799284289642284287028617 2099463217231713215271463)
                      ·
                        rfl

theorem cell23_4088690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_4088690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088690 prefixEnd_4088690 := by exact prefixLift 4088690
  have htrace : WordTrace (prefixWord ++ tailWord_4088690) baseStart_4088690 baseEnd_4088690 := by
    simpa [prefixWord, tailWord_4088690, baseEnd_4088690] using wordTrace_append hprefix tailTrace_4088690
  have hstable : (prefixWord ++ tailWord_4088690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088690).length < 2 ^ (prefixWord ++ tailWord_4088690).sum := by decide
  have hdescent : baseEnd_4088690 < baseStart_4088690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088693 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_4088693 : Nat := 118140960795 + 4088693 * 2 ^ 59
def prefixEnd_4088693 : Nat := 4983230072969 + 3 ^ 40 * 4088693 * 2
def baseEnd_4088693 : Nat := 2099464757673676703533949

theorem tailTrace_4088693 : CollatzResearch.WordTrace tailWord_4088693 prefixEnd_4088693 2099464757673676703533949 := by
  unfold tailWord_4088693
  simp only [CollatzResearch.WordTrace]
  refine ⟨149126884976371029015550733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99417923317580686010367155 149126884976371029015550733)
  ·
    refine ⟨55922581866139135880831525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149126884976371029015550733 55922581866139135880831525)
    ·
      refine ⟨10485484099901087977655911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55922581866139135880831525 10485484099901087977655911)
      ·
        refine ⟨15728226149851631966483867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10485484099901087977655911 15728226149851631966483867)
        ·
          refine ⟨23592339224777447949725801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15728226149851631966483867 23592339224777447949725801)
          ·
            refine ⟨17694254418583085962294351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23592339224777447949725801 17694254418583085962294351)
            ·
              refine ⟨26541381627874628943441527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17694254418583085962294351 26541381627874628943441527)
              ·
                refine ⟨39812072441811943415162291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26541381627874628943441527 39812072441811943415162291)
                ·
                  refine ⟨59718108662717915122743437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39812072441811943415162291 59718108662717915122743437)
                  ·
                    refine ⟨22394290748519218171028789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59718108662717915122743437 22394290748519218171028789)
                    ·
                      refine ⟨2099464757673676703533949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22394290748519218171028789 2099464757673676703533949)
                      ·
                        rfl

theorem cell23_4088693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_4088693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088693 prefixEnd_4088693 := by exact prefixLift 4088693
  have htrace : WordTrace (prefixWord ++ tailWord_4088693) baseStart_4088693 baseEnd_4088693 := by
    simpa [prefixWord, tailWord_4088693, baseEnd_4088693] using wordTrace_append hprefix tailTrace_4088693
  have hstable : (prefixWord ++ tailWord_4088693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088693).length < 2 ^ (prefixWord ++ tailWord_4088693).sum := by decide
  have hdescent : baseEnd_4088693 < baseStart_4088693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088694 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4088694 : Nat := 118140960795 + 4088694 * 2 ^ 59
def prefixEnd_4088694 : Nat := 4983230072969 + 3 ^ 40 * 4088694 * 2
def baseEnd_4088694 : Nat := 2099465271154331199621445

theorem tailTrace_4088694 : CollatzResearch.WordTrace tailWord_4088694 prefixEnd_4088694 2099465271154331199621445 := by
  unfold tailWord_4088694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320432590585462886646071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99417947632911604124224757 9320432590585462886646071)
  ·
    refine ⟨13980648885878194329969107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9320432590585462886646071 13980648885878194329969107)
    ·
      refine ⟨20970973328817291494953661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13980648885878194329969107 20970973328817291494953661)
      ·
        refine ⟨7864114998306484310607623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20970973328817291494953661 7864114998306484310607623)
        ·
          refine ⟨11796172497459726465911435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7864114998306484310607623 11796172497459726465911435)
          ·
            refine ⟨17694258746189589698867153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11796172497459726465911435 17694258746189589698867153)
            ·
              refine ⟨13270694059642192274150365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17694258746189589698867153 13270694059642192274150365)
              ·
                refine ⟨4976510272365822102806387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13270694059642192274150365 4976510272365822102806387)
                ·
                  refine ⟨7464765408548733154209581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976510272365822102806387 7464765408548733154209581)
                  ·
                    refine ⟨2799287028205774932828593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7464765408548733154209581 2799287028205774932828593)
                    ·
                      refine ⟨2099465271154331199621445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799287028205774932828593 2099465271154331199621445)
                      ·
                        rfl

theorem cell23_4088694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4088694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088694 prefixEnd_4088694 := by exact prefixLift 4088694
  have htrace : WordTrace (prefixWord ++ tailWord_4088694) baseStart_4088694 baseEnd_4088694 := by
    simpa [prefixWord, tailWord_4088694, baseEnd_4088694] using wordTrace_append hprefix tailTrace_4088694
  have hstable : (prefixWord ++ tailWord_4088694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088694).length < 2 ^ (prefixWord ++ tailWord_4088694).sum := by decide
  have hdescent : baseEnd_4088694 < baseStart_4088694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088707 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 2, 2, 2]
def baseStart_4088707 : Nat := 118140960795 + 4088707 * 2 ^ 59
def prefixEnd_4088707 : Nat := 4983230072969 + 3 ^ 40 * 4088707 * 2
def baseEnd_4088707 : Nat := 2099471946402839648758885

theorem tailTrace_4088707 : CollatzResearch.WordTrace tailWord_4088707 prefixEnd_4088707 2099471946402839648758885 := by
  unfold tailWord_4088707
  simp only [CollatzResearch.WordTrace]
  refine ⟨149127395598320309406560375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99418263732213539604373583 149127395598320309406560375)
  ·
    refine ⟨223691093397480464109840563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149127395598320309406560375 223691093397480464109840563)
    ·
      refine ⟨335536640096220696164760845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223691093397480464109840563 335536640096220696164760845)
      ·
        refine ⟨125826240036082761061785317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335536640096220696164760845 125826240036082761061785317)
        ·
          refine ⟨23592420006765517699084747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125826240036082761061785317 23592420006765517699084747)
          ·
            refine ⟨35388630010148276548627121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23592420006765517699084747 35388630010148276548627121)
            ·
              refine ⟨26541472507611207411470341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35388630010148276548627121 26541472507611207411470341)
              ·
                refine ⟨4976526095177101389650689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26541472507611207411470341 4976526095177101389650689)
                ·
                  refine ⟨3732394571382826042238017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4976526095177101389650689 3732394571382826042238017)
                  ·
                    refine ⟨2799295928537119531678513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3732394571382826042238017 2799295928537119531678513)
                    ·
                      refine ⟨2099471946402839648758885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799295928537119531678513 2099471946402839648758885)
                      ·
                        rfl

theorem cell23_4088707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 2, 2].length) (baseStart_4088707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088707 prefixEnd_4088707 := by exact prefixLift 4088707
  have htrace : WordTrace (prefixWord ++ tailWord_4088707) baseStart_4088707 baseEnd_4088707 := by
    simpa [prefixWord, tailWord_4088707, baseEnd_4088707] using wordTrace_append hprefix tailTrace_4088707
  have hstable : (prefixWord ++ tailWord_4088707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088707).length < 2 ^ (prefixWord ++ tailWord_4088707).sum := by decide
  have hdescent : baseEnd_4088707 < baseStart_4088707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088713 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 7]
def baseStart_4088713 : Nat := 118140960795 + 4088713 * 2 ^ 59
def prefixEnd_4088713 : Nat := 4983230072969 + 3 ^ 40 * 4088713 * 2
def baseEnd_4088713 : Nat := 233275003031862958364873

theorem tailTrace_4088713 : CollatzResearch.WordTrace tailWord_4088713 prefixEnd_4088713 233275003031862958364873 := by
  unfold tailWord_4088713
  simp only [CollatzResearch.WordTrace]
  refine ⟨149127614436298572431278793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99418409624199048287519195 149127614436298572431278793)
  ·
    refine ⟨111845710827223929323459095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149127614436298572431278793 111845710827223929323459095)
    ·
      refine ⟨167768566240835893985188643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111845710827223929323459095 167768566240835893985188643)
      ·
        refine ⟨251652849361253840977782965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167768566240835893985188643 251652849361253840977782965)
        ·
          refine ⟨23592454627617547591667153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251652849361253840977782965 23592454627617547591667153)
          ·
            refine ⟨17694340970713160693750365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23592454627617547591667153 17694340970713160693750365)
            ·
              refine ⟨6635377864017435260156387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17694340970713160693750365 6635377864017435260156387)
              ·
                refine ⟨9953066796026152890234581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6635377864017435260156387 9953066796026152890234581)
                ·
                  refine ⟨233275003031862958364873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9953066796026152890234581 233275003031862958364873)
                  ·
                    rfl

theorem cell23_4088713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 7].length) (baseStart_4088713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088713 prefixEnd_4088713 := by exact prefixLift 4088713
  have htrace : WordTrace (prefixWord ++ tailWord_4088713) baseStart_4088713 baseEnd_4088713 := by
    simpa [prefixWord, tailWord_4088713, baseEnd_4088713] using wordTrace_append hprefix tailTrace_4088713
  have hstable : (prefixWord ++ tailWord_4088713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088713).length < 2 ^ (prefixWord ++ tailWord_4088713).sum := by decide
  have hdescent : baseEnd_4088713 < baseStart_4088713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088724 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_4088724 : Nat := 118140960795 + 4088724 * 2 ^ 59
def prefixEnd_4088724 : Nat := 4983230072969 + 3 ^ 40 * 4088724 * 2
def baseEnd_4088724 : Nat := 2099480675573966082246307

theorem tailTrace_4088724 : CollatzResearch.WordTrace tailWord_4088724 prefixEnd_4088724 2099480675573966082246307 := by
  unfold tailWord_4088724
  simp only [CollatzResearch.WordTrace]
  refine ⟨74564007819629360654964613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99418677092839147539952817 74564007819629360654964613)
  ·
    refine ⟨13980751466180505122805865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74564007819629360654964613 13980751466180505122805865)
    ·
      refine ⟨10485563599635378842104399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13980751466180505122805865 10485563599635378842104399)
      ·
        refine ⟨15728345399453068263156599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10485563599635378842104399 15728345399453068263156599)
        ·
          refine ⟨23592518099179602394734899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15728345399453068263156599 23592518099179602394734899)
          ·
            refine ⟨35388777148769403592102349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23592518099179602394734899 35388777148769403592102349)
            ·
              refine ⟨13270791430788526347038381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35388777148769403592102349 13270791430788526347038381)
              ·
                refine ⟨4976546786545697380139393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13270791430788526347038381 4976546786545697380139393)
                ·
                  refine ⟨3732410089909273035104545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4976546786545697380139393 3732410089909273035104545)
                  ·
                    refine ⟨2799307567431954776328409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3732410089909273035104545 2799307567431954776328409)
                    ·
                      refine ⟨2099480675573966082246307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799307567431954776328409 2099480675573966082246307)
                      ·
                        rfl

theorem cell23_4088724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_4088724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088724 prefixEnd_4088724 := by exact prefixLift 4088724
  have htrace : WordTrace (prefixWord ++ tailWord_4088724) baseStart_4088724 baseEnd_4088724 := by
    simpa [prefixWord, tailWord_4088724, baseEnd_4088724] using wordTrace_append hprefix tailTrace_4088724
  have hstable : (prefixWord ++ tailWord_4088724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088724).length < 2 ^ (prefixWord ++ tailWord_4088724).sum := by decide
  have hdescent : baseEnd_4088724 < baseStart_4088724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088797 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_4088797 : Nat := 118140960795 + 4088797 * 2 ^ 59
def prefixEnd_4088797 : Nat := 4983230072969 + 3 ^ 40 * 4088797 * 2
def baseEnd_4088797 : Nat := 2099518159661744296633471

theorem tailTrace_4088797 : CollatzResearch.WordTrace tailWord_4088797 prefixEnd_4088797 2099518159661744296633471 := by
  unfold tailWord_4088797
  simp only [CollatzResearch.WordTrace]
  refine ⟨149130678167994254777336645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99420452111996169851557763 149130678167994254777336645)
  ·
    refine ⟨27962002156498922770750621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149130678167994254777336645 27962002156498922770750621)
    ·
      refine ⟨10485750808687096039031483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27962002156498922770750621 10485750808687096039031483)
      ·
        refine ⟨15728626213030644058547225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10485750808687096039031483 15728626213030644058547225)
        ·
          refine ⟨11796469659772983043910419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15728626213030644058547225 11796469659772983043910419)
          ·
            refine ⟨17694704489659474565865629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11796469659772983043910419 17694704489659474565865629)
            ·
              refine ⟨6635514183622302962199611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17694704489659474565865629 6635514183622302962199611)
              ·
                refine ⟨9953271275433454443299417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6635514183622302962199611 9953271275433454443299417)
                ·
                  refine ⟨7464953456575090832474563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9953271275433454443299417 7464953456575090832474563)
                  ·
                    refine ⟨11197430184862636248711845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464953456575090832474563 11197430184862636248711845)
                    ·
                      refine ⟨2099518159661744296633471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11197430184862636248711845 2099518159661744296633471)
                      ·
                        rfl

theorem cell23_4088797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_4088797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088797 prefixEnd_4088797 := by exact prefixLift 4088797
  have htrace : WordTrace (prefixWord ++ tailWord_4088797) baseStart_4088797 baseEnd_4088797 := by
    simpa [prefixWord, tailWord_4088797, baseEnd_4088797] using wordTrace_append hprefix tailTrace_4088797
  have hstable : (prefixWord ++ tailWord_4088797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088797).length < 2 ^ (prefixWord ++ tailWord_4088797).sum := by decide
  have hdescent : baseEnd_4088797 < baseStart_4088797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088803 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 8]
def baseStart_4088803 : Nat := 118140960795 + 4088803 * 2 ^ 59
def prefixEnd_4088803 : Nat := 4983230072969 + 3 ^ 40 * 4088803 * 2
def baseEnd_4088803 : Nat := 233280137838407919239827

theorem tailTrace_4088803 : CollatzResearch.WordTrace tailWord_4088803 prefixEnd_4088803 233280137838407919239827 := by
  unfold tailWord_4088803
  simp only [CollatzResearch.WordTrace]
  refine ⟨149130897005972517802055063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99420598003981678534703375 149130897005972517802055063)
  ·
    refine ⟨223696345508958776703082595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149130897005972517802055063 223696345508958776703082595)
    ·
      refine ⟨335544518263438165054623893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223696345508958776703082595 335544518263438165054623893)
      ·
        refine ⟨15728649293598663986935495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 335544518263438165054623893 15728649293598663986935495)
        ·
          refine ⟨23592973940397995980403243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15728649293598663986935495 23592973940397995980403243)
          ·
            refine ⟨35389460910596993970604865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23592973940397995980403243 35389460910596993970604865)
            ·
              refine ⟨26542095682947745477953649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35389460910596993970604865 26542095682947745477953649)
              ·
                refine ⟨19906571762210809108465237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26542095682947745477953649 19906571762210809108465237)
                ·
                  refine ⟨233280137838407919239827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19906571762210809108465237 233280137838407919239827)
                  ·
                    rfl

theorem cell23_4088803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 8].length) (baseStart_4088803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088803 prefixEnd_4088803 := by exact prefixLift 4088803
  have htrace : WordTrace (prefixWord ++ tailWord_4088803) baseStart_4088803 baseEnd_4088803 := by
    simpa [prefixWord, tailWord_4088803, baseEnd_4088803] using wordTrace_append hprefix tailTrace_4088803
  have hstable : (prefixWord ++ tailWord_4088803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088803).length < 2 ^ (prefixWord ++ tailWord_4088803).sum := by decide
  have hdescent : baseEnd_4088803 < baseStart_4088803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088880 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 4, 4]
def baseStart_4088880 : Nat := 118140960795 + 4088880 * 2 ^ 59
def prefixEnd_4088880 : Nat := 4983230072969 + 3 ^ 40 * 4088880 * 2
def baseEnd_4088880 : Nat := 699853592852022490631863

theorem tailTrace_4088880 : CollatzResearch.WordTrace tailWord_4088880 prefixEnd_4088880 699853592852022490631863 := by
  unfold tailWord_4088880
  simp only [CollatzResearch.WordTrace]
  refine ⟨74566852713346779976304047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99422470284462373301738729 74566852713346779976304047)
  ·
    refine ⟨111850279070020169964456071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74566852713346779976304047 111850279070020169964456071)
    ·
      refine ⟨167775418605030254946684107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111850279070020169964456071 167775418605030254946684107)
      ·
        refine ⟨251663127907545382420026161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167775418605030254946684107 251663127907545382420026161)
        ·
          refine ⟨188747345930659036815019621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251663127907545382420026161 188747345930659036815019621)
          ·
            refine ⟨35390127361998569402816179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188747345930659036815019621 35390127361998569402816179)
            ·
              refine ⟨53085191042997854104224269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35390127361998569402816179 53085191042997854104224269)
              ·
                refine ⟨19906946641124195289084101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53085191042997854104224269 19906946641124195289084101)
                ·
                  refine ⟨3732552495210786616703269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19906946641124195289084101 3732552495210786616703269)
                  ·
                    refine ⟨699853592852022490631863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3732552495210786616703269 699853592852022490631863)
                    ·
                      rfl

theorem cell23_4088880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4, 4].length) (baseStart_4088880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088880 prefixEnd_4088880 := by exact prefixLift 4088880
  have htrace : WordTrace (prefixWord ++ tailWord_4088880) baseStart_4088880 baseEnd_4088880 := by
    simpa [prefixWord, tailWord_4088880, baseEnd_4088880] using wordTrace_append hprefix tailTrace_4088880
  have hstable : (prefixWord ++ tailWord_4088880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088880).length < 2 ^ (prefixWord ++ tailWord_4088880).sum := by decide
  have hdescent : baseEnd_4088880 < baseStart_4088880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088881 : List Nat := [1, 2, 2, 3, 1, 2, 5, 2, 1, 1, 3]
def baseStart_4088881 : Nat := 118140960795 + 4088881 * 2 ^ 59
def prefixEnd_4088881 : Nat := 4983230072969 + 3 ^ 40 * 4088881 * 2
def baseEnd_4088881 : Nat := 2099561292036721967983085

theorem tailTrace_4088881 : CollatzResearch.WordTrace tailWord_4088881 prefixEnd_4088881 2099561292036721967983085 := by
  unfold tailWord_4088881
  simp only [CollatzResearch.WordTrace]
  refine ⟨149133741899689937123394497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99422494599793291415596331 149133741899689937123394497)
  ·
    refine ⟨111850306424767452842545873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149133741899689937123394497 111850306424767452842545873)
    ·
      refine ⟨83887729818575589631909405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111850306424767452842545873 83887729818575589631909405)
      ·
        refine ⟨31457898681965846111966027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83887729818575589631909405 31457898681965846111966027)
        ·
          refine ⟨47186848022948769167949041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31457898681965846111966027 47186848022948769167949041)
          ·
            refine ⟨35390136017211576875961781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47186848022948769167949041 35390136017211576875961781)
            ·
              refine ⟨3317825251613585332121417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35390136017211576875961781 3317825251613585332121417)
              ·
                refine ⟨2488368938710188999091063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317825251613585332121417 2488368938710188999091063)
                ·
                  refine ⟨3732553408065283498636595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488368938710188999091063 3732553408065283498636595)
                  ·
                    refine ⟨5598830112097925247954893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3732553408065283498636595 5598830112097925247954893)
                    ·
                      refine ⟨2099561292036721967983085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5598830112097925247954893 2099561292036721967983085)
                      ·
                        rfl

theorem cell23_4088881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_4088881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088881 prefixEnd_4088881 := by exact prefixLift 4088881
  have htrace : WordTrace (prefixWord ++ tailWord_4088881) baseStart_4088881 baseEnd_4088881 := by
    simpa [prefixWord, tailWord_4088881, baseEnd_4088881] using wordTrace_append hprefix tailTrace_4088881
  have hstable : (prefixWord ++ tailWord_4088881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088881).length < 2 ^ (prefixWord ++ tailWord_4088881).sum := by decide
  have hdescent : baseEnd_4088881 < baseStart_4088881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088890 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_4088890 : Nat := 118140960795 + 4088890 * 2 ^ 59
def prefixEnd_4088890 : Nat := 4983230072969 + 3 ^ 40 * 4088890 * 2
def baseEnd_4088890 : Nat := 2099565913362612432770543

theorem tailTrace_4088890 : CollatzResearch.WordTrace tailWord_4088890 prefixEnd_4088890 2099565913362612432770543 := by
  unfold tailWord_4088890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37283517539164332915118031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99422713437771554440314749 37283517539164332915118031)
  ·
    refine ⟨55925276308746499372677047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37283517539164332915118031 55925276308746499372677047)
    ·
      refine ⟨83887914463119749059015571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55925276308746499372677047 83887914463119749059015571)
      ·
        refine ⟨125831871694679623588523357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83887914463119749059015571 125831871694679623588523357)
        ·
          refine ⟨47186951885504858845696259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125831871694679623588523357 47186951885504858845696259)
          ·
            refine ⟨70780427828257288268544389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47186951885504858845696259 70780427828257288268544389)
            ·
              refine ⟨13271330217798241550352073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70780427828257288268544389 13271330217798241550352073)
              ·
                refine ⟨9953497663348681162764055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13271330217798241550352073 9953497663348681162764055)
                ·
                  refine ⟨14930246495023021744146083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9953497663348681162764055 14930246495023021744146083)
                  ·
                    refine ⟨22395369742534532616219125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14930246495023021744146083 22395369742534532616219125)
                    ·
                      refine ⟨2099565913362612432770543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22395369742534532616219125 2099565913362612432770543)
                      ·
                        rfl

theorem cell23_4088890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_4088890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088890 prefixEnd_4088890 := by exact prefixLift 4088890
  have htrace : WordTrace (prefixWord ++ tailWord_4088890) baseStart_4088890 baseEnd_4088890 := by
    simpa [prefixWord, tailWord_4088890, baseEnd_4088890] using wordTrace_append hprefix tailTrace_4088890
  have hstable : (prefixWord ++ tailWord_4088890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088890).length < 2 ^ (prefixWord ++ tailWord_4088890).sum := by decide
  have hdescent : baseEnd_4088890 < baseStart_4088890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088918 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_4088918 : Nat := 118140960795 + 4088918 * 2 ^ 59
def prefixEnd_4088918 : Nat := 4983230072969 + 3 ^ 40 * 4088918 * 2
def baseEnd_4088918 : Nat := 699860096940312774406805

theorem tailTrace_4088918 : CollatzResearch.WordTrace tailWord_4088918 prefixEnd_4088918 699860096940312774406805 := by
  unfold tailWord_4088918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320943212534743277655713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99423394267037261628327605 9320943212534743277655713)
  ·
    refine ⟨6990707409401057458241785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9320943212534743277655713 6990707409401057458241785)
    ·
      refine ⟨5243030557050793093681339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6990707409401057458241785 5243030557050793093681339)
      ·
        refine ⟨7864545835576189640522009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243030557050793093681339 7864545835576189640522009)
        ·
          refine ⟨5898409376682142230391507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7864545835576189640522009 5898409376682142230391507)
          ·
            refine ⟨8847614065023213345587261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5898409376682142230391507 8847614065023213345587261)
            ·
              refine ⟨3317855274383705004595223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8847614065023213345587261 3317855274383705004595223)
              ·
                refine ⟨4976782911575557506892835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3317855274383705004595223 4976782911575557506892835)
                ·
                  refine ⟨7465174367363336260339253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976782911575557506892835 7465174367363336260339253)
                  ·
                    refine ⟨699860096940312774406805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7465174367363336260339253 699860096940312774406805)
                    ·
                      rfl

theorem cell23_4088918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_4088918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088918 prefixEnd_4088918 := by exact prefixLift 4088918
  have htrace : WordTrace (prefixWord ++ tailWord_4088918) baseStart_4088918 baseEnd_4088918 := by
    simpa [prefixWord, tailWord_4088918, baseEnd_4088918] using wordTrace_append hprefix tailTrace_4088918
  have hstable : (prefixWord ++ tailWord_4088918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088918).length < 2 ^ (prefixWord ++ tailWord_4088918).sum := by decide
  have hdescent : baseEnd_4088918 < baseStart_4088918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088938 : List Nat := [3, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_4088938 : Nat := 118140960795 + 4088938 * 2 ^ 59
def prefixEnd_4088938 : Nat := 4983230072969 + 3 ^ 40 * 4088938 * 2
def baseEnd_4088938 : Nat := 2099590560434028244970323

theorem tailTrace_4088938 : CollatzResearch.WordTrace tailWord_4088938 prefixEnd_4088938 2099590560434028244970323 := by
  unfold tailWord_4088938
  simp only [CollatzResearch.WordTrace]
  refine ⟨37283955215120858964554867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99423880573655623905479645 37283955215120858964554867)
  ·
    refine ⟨55925932822681288446832301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37283955215120858964554867 55925932822681288446832301)
    ·
      refine ⟨20972224808505483167562113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55925932822681288446832301 20972224808505483167562113)
      ·
        refine ⟨15729168606379112375671585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20972224808505483167562113 15729168606379112375671585)
        ·
          refine ⟨11796876454784334281753689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15729168606379112375671585 11796876454784334281753689)
          ·
            refine ⟨8847657341088250711315267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11796876454784334281753689 8847657341088250711315267)
            ·
              refine ⟨13271486011632376066972901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8847657341088250711315267 13271486011632376066972901)
              ·
                refine ⟨2488403627181070512557419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13271486011632376066972901 2488403627181070512557419)
                ·
                  refine ⟨3732605440771605768836129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488403627181070512557419 3732605440771605768836129)
                  ·
                    refine ⟨2799454080578704326627097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3732605440771605768836129 2799454080578704326627097)
                    ·
                      refine ⟨2099590560434028244970323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799454080578704326627097 2099590560434028244970323)
                      ·
                        rfl

theorem cell23_4088938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_4088938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088938 prefixEnd_4088938 := by exact prefixLift 4088938
  have htrace : WordTrace (prefixWord ++ tailWord_4088938) baseStart_4088938 baseEnd_4088938 := by
    simpa [prefixWord, tailWord_4088938, baseEnd_4088938] using wordTrace_append hprefix tailTrace_4088938
  have hstable : (prefixWord ++ tailWord_4088938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088938).length < 2 ^ (prefixWord ++ tailWord_4088938).sum := by decide
  have hdescent : baseEnd_4088938 < baseStart_4088938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088964 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_4088964 : Nat := 118140960795 + 4088964 * 2 ^ 59
def prefixEnd_4088964 : Nat := 4983230072969 + 3 ^ 40 * 4088964 * 2
def baseEnd_4088964 : Nat := 2099603910931045143245203

theorem tailTrace_4088964 : CollatzResearch.WordTrace tailWord_4088964 prefixEnd_4088964 2099603910931045143245203 := by
  unfold tailWord_4088964
  simp only [CollatzResearch.WordTrace]
  refine ⟨74568384579194621149332973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99424512772259494865777297 74568384579194621149332973)
  ·
    refine ⟨27963144217197982930999865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74568384579194621149332973 27963144217197982930999865)
    ·
      refine ⟨20972358162898487198249899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27963144217197982930999865 20972358162898487198249899)
      ·
        refine ⟨31458537244347730797374849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20972358162898487198249899 31458537244347730797374849)
        ·
          refine ⟨23593902933260798098031137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31458537244347730797374849 23593902933260798098031137)
          ·
            refine ⟨17695427199945598573523353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23593902933260798098031137 17695427199945598573523353)
            ·
              refine ⟨13271570399959198930142515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17695427199945598573523353 13271570399959198930142515)
              ·
                refine ⟨19907355599938798395213773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13271570399959198930142515 19907355599938798395213773)
                ·
                  refine ⟨7465258349977049398205165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19907355599938798395213773 7465258349977049398205165)
                  ·
                    refine ⟨2799471881241393524326937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7465258349977049398205165 2799471881241393524326937)
                    ·
                      refine ⟨2099603910931045143245203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799471881241393524326937 2099603910931045143245203)
                      ·
                        rfl

theorem cell23_4088964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_4088964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088964 prefixEnd_4088964 := by exact prefixLift 4088964
  have htrace : WordTrace (prefixWord ++ tailWord_4088964) baseStart_4088964 baseEnd_4088964 := by
    simpa [prefixWord, tailWord_4088964, baseEnd_4088964] using wordTrace_append hprefix tailTrace_4088964
  have hstable : (prefixWord ++ tailWord_4088964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088964).length < 2 ^ (prefixWord ++ tailWord_4088964).sum := by decide
  have hdescent : baseEnd_4088964 < baseStart_4088964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4088970 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_4088970 : Nat := 118140960795 + 4088970 * 2 ^ 59
def prefixEnd_4088970 : Nat := 4983230072969 + 3 ^ 40 * 4088970 * 2
def baseEnd_4088970 : Nat := 699868997271657373256725

theorem tailTrace_4088970 : CollatzResearch.WordTrace tailWord_4088970 prefixEnd_4088970 699868997271657373256725 := by
  unfold tailWord_4088970
  simp only [CollatzResearch.WordTrace]
  refine ⟨37284246999091876330846091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99424658664245003548922909 37284246999091876330846091)
  ·
    refine ⟨55926370498637814496269137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37284246999091876330846091 55926370498637814496269137)
    ·
      refine ⟨41944777873978360872201853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55926370498637814496269137 41944777873978360872201853)
      ·
        refine ⟨15729291702741885327075695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41944777873978360872201853 15729291702741885327075695)
        ·
          refine ⟨23593937554112827990613543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15729291702741885327075695 23593937554112827990613543)
          ·
            refine ⟨35390906331169241985920315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23593937554112827990613543 35390906331169241985920315)
            ·
              refine ⟨53086359496753862978880473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35390906331169241985920315 53086359496753862978880473)
              ·
                refine ⟨39814769622565397234160355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53086359496753862978880473 39814769622565397234160355)
                ·
                  refine ⟨59722154433848095851240533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39814769622565397234160355 59722154433848095851240533)
                  ·
                    refine ⟨699868997271657373256725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59722154433848095851240533 699868997271657373256725)
                    ·
                      rfl

theorem cell23_4088970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_4088970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4088970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4088970 prefixEnd_4088970 := by exact prefixLift 4088970
  have htrace : WordTrace (prefixWord ++ tailWord_4088970) baseStart_4088970 baseEnd_4088970 := by
    simpa [prefixWord, tailWord_4088970, baseEnd_4088970] using wordTrace_append hprefix tailTrace_4088970
  have hstable : (prefixWord ++ tailWord_4088970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4088970).length < 2 ^ (prefixWord ++ tailWord_4088970).sum := by decide
  have hdescent : baseEnd_4088970 < baseStart_4088970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4088970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089034 : List Nat := [3, 1, 2, 1, 3, 2, 3, 3, 5]
def baseStart_4089034 : Nat := 118140960795 + 4089034 * 2 ^ 59
def prefixEnd_4089034 : Nat := 4983230072969 + 3 ^ 40 * 4089034 * 2
def baseEnd_4089034 : Nat := 233293317175206652152209

theorem tailTrace_4089034 : CollatzResearch.WordTrace tailWord_4089034 prefixEnd_4089034 233293317175206652152209 := by
  unfold tailWord_4089034
  simp only [CollatzResearch.WordTrace]
  refine ⟨37284830567033911063428539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99426214845423762835809437 37284830567033911063428539)
  ·
    refine ⟨55927245850550866595142809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37284830567033911063428539 55927245850550866595142809)
    ·
      refine ⟨41945434387913149946357107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55927245850550866595142809 41945434387913149946357107)
      ·
        refine ⟨62918151581869724919535661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41945434387913149946357107 62918151581869724919535661)
        ·
          refine ⟨23594306843201146844825873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62918151581869724919535661 23594306843201146844825873)
          ·
            refine ⟨17695730132400860133619405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23594306843201146844825873 17695730132400860133619405)
            ·
              refine ⟨6635898799650322550107277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17695730132400860133619405 6635898799650322550107277)
              ·
                refine ⟨2488462049868870956290229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6635898799650322550107277 2488462049868870956290229)
                ·
                  refine ⟨233293317175206652152209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2488462049868870956290229 233293317175206652152209)
                  ·
                    rfl

theorem cell23_4089034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_4089034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089034 prefixEnd_4089034 := by exact prefixLift 4089034
  have htrace : WordTrace (prefixWord ++ tailWord_4089034) baseStart_4089034 baseEnd_4089034 := by
    simpa [prefixWord, tailWord_4089034, baseEnd_4089034] using wordTrace_append hprefix tailTrace_4089034
  have hstable : (prefixWord ++ tailWord_4089034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089034).length < 2 ^ (prefixWord ++ tailWord_4089034).sum := by decide
  have hdescent : baseEnd_4089034 < baseStart_4089034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089057 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_4089057 : Nat := 118140960795 + 4089057 * 2 ^ 59
def prefixEnd_4089057 : Nat := 4983230072969 + 3 ^ 40 * 4089057 * 2
def baseEnd_4089057 : Nat := 2099651664631913279382275

theorem tailTrace_4089057 : CollatzResearch.WordTrace tailWord_4089057 prefixEnd_4089057 2099651664631913279382275 := by
  unfold tailWord_4089057
  simp only [CollatzResearch.WordTrace]
  refine ⟨149140161147052319181801425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99426774098034879454534283 149140161147052319181801425)
  ·
    refine ⟨111855120860289239386351069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149140161147052319181801425 111855120860289239386351069)
    ·
      refine ⟨41945670322608464769881651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111855120860289239386351069 41945670322608464769881651)
      ·
        refine ⟨62918505483912697154822477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41945670322608464769881651 62918505483912697154822477)
        ·
          refine ⟨23594439556467261433058429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62918505483912697154822477 23594439556467261433058429)
          ·
            refine ⟨8847914833675223037396911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23594439556467261433058429 8847914833675223037396911)
            ·
              refine ⟨13271872250512834556095367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8847914833675223037396911 13271872250512834556095367)
              ·
                refine ⟨19907808375769251834143051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13271872250512834556095367 19907808375769251834143051)
                ·
                  refine ⟨29861712563653877751214577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19907808375769251834143051 29861712563653877751214577)
                  ·
                    refine ⟨22396284422740408313410933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29861712563653877751214577 22396284422740408313410933)
                    ·
                      refine ⟨2099651664631913279382275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22396284422740408313410933 2099651664631913279382275)
                      ·
                        rfl

theorem cell23_4089057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_4089057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089057 prefixEnd_4089057 := by exact prefixLift 4089057
  have htrace : WordTrace (prefixWord ++ tailWord_4089057) baseStart_4089057 baseEnd_4089057 := by
    simpa [prefixWord, tailWord_4089057, baseEnd_4089057] using wordTrace_append hprefix tailTrace_4089057
  have hstable : (prefixWord ++ tailWord_4089057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089057).length < 2 ^ (prefixWord ++ tailWord_4089057).sum := by decide
  have hdescent : baseEnd_4089057 < baseStart_4089057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089080 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_4089080 : Nat := 118140960795 + 4089080 * 2 ^ 59
def prefixEnd_4089080 : Nat := 4983230072969 + 3 ^ 40 * 4089080 * 2
def baseEnd_4089080 : Nat := 2099663474686966689394669

theorem tailTrace_4089080 : CollatzResearch.WordTrace tailWord_4089080 prefixEnd_4089080 2099663474686966689394669 := by
  unfold tailWord_4089080
  simp only [CollatzResearch.WordTrace]
  refine ⟨74570500012984497054944347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99427333350645996073259129 74570500012984497054944347)
  ·
    refine ⟨111855750019476745582416521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74570500012984497054944347 111855750019476745582416521)
    ·
      refine ⟨83891812514607559186812391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111855750019476745582416521 83891812514607559186812391)
      ·
        refine ⟨125837718771911338780218587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83891812514607559186812391 125837718771911338780218587)
        ·
          refine ⟨188756578157867008170327881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125837718771911338780218587 188756578157867008170327881)
          ·
            refine ⟨141567433618400256127745911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188756578157867008170327881 141567433618400256127745911)
            ·
              refine ⟨212351150427600384191618867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141567433618400256127745911 212351150427600384191618867)
              ·
                refine ⟨318526725641400576287428301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212351150427600384191618867 318526725641400576287428301)
                ·
                  refine ⟨119447522115525216107785613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318526725641400576287428301 119447522115525216107785613)
                  ·
                    refine ⟨44792820793321956040419605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119447522115525216107785613 44792820793321956040419605)
                    ·
                      refine ⟨2099663474686966689394669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44792820793321956040419605 2099663474686966689394669)
                      ·
                        rfl

theorem cell23_4089080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_4089080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089080 prefixEnd_4089080 := by exact prefixLift 4089080
  have htrace : WordTrace (prefixWord ++ tailWord_4089080) baseStart_4089080 baseEnd_4089080 := by
    simpa [prefixWord, tailWord_4089080, baseEnd_4089080] using wordTrace_append hprefix tailTrace_4089080
  have hstable : (prefixWord ++ tailWord_4089080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089080).length < 2 ^ (prefixWord ++ tailWord_4089080).sum := by decide
  have hdescent : baseEnd_4089080 < baseStart_4089080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089111 : List Nat := [1, 1, 3, 4, 1, 1, 3, 4, 1, 4]
def baseStart_4089111 : Nat := 118140960795 + 4089111 * 2 ^ 59
def prefixEnd_4089111 : Nat := 4983230072969 + 3 ^ 40 * 4089111 * 2
def baseEnd_4089111 : Nat := 699893130862418689369009

theorem tailTrace_4089111 : CollatzResearch.WordTrace tailWord_4089111 prefixEnd_4089111 699893130862418689369009 := by
  unfold tailWord_4089111
  simp only [CollatzResearch.WordTrace]
  refine ⟨149142130688856686404267187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99428087125904457602844791 149142130688856686404267187)
  ·
    refine ⟨223713196033285029606400781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149142130688856686404267187 223713196033285029606400781)
    ·
      refine ⟨83892448512481886102400293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223713196033285029606400781 83892448512481886102400293)
      ·
        refine ⟨15729834096090353644200055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83892448512481886102400293 15729834096090353644200055)
        ·
          refine ⟨23594751144135530466300083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15729834096090353644200055 23594751144135530466300083)
          ·
            refine ⟨35392126716203295699450125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23594751144135530466300083 35392126716203295699450125)
            ·
              refine ⟨13272047518576235887293797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35392126716203295699450125 13272047518576235887293797)
              ·
                refine ⟨2488508909733044228867587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13272047518576235887293797 2488508909733044228867587)
                ·
                  refine ⟨3732763364599566343301381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488508909733044228867587 3732763364599566343301381)
                  ·
                    refine ⟨699893130862418689369009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3732763364599566343301381 699893130862418689369009)
                    ·
                      rfl

theorem cell23_4089111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_4089111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089111 prefixEnd_4089111 := by exact prefixLift 4089111
  have htrace : WordTrace (prefixWord ++ tailWord_4089111) baseStart_4089111 baseEnd_4089111 := by
    simpa [prefixWord, tailWord_4089111, baseEnd_4089111] using wordTrace_append hprefix tailTrace_4089111
  have hstable : (prefixWord ++ tailWord_4089111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089111).length < 2 ^ (prefixWord ++ tailWord_4089111).sum := by decide
  have hdescent : baseEnd_4089111 < baseStart_4089111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089158 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_4089158 : Nat := 118140960795 + 4089158 * 2 ^ 59
def prefixEnd_4089158 : Nat := 4983230072969 + 3 ^ 40 * 4089158 * 2
def baseEnd_4089158 : Nat := 233300391797557487135479

theorem tailTrace_4089158 : CollatzResearch.WordTrace tailWord_4089158 prefixEnd_4089158 233300391797557487135479 := by
  unfold tailWord_4089158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660745153740200419725879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99429229946457608954152085 4660745153740200419725879)
  ·
    refine ⟨6991117730610300629588819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4660745153740200419725879 6991117730610300629588819)
    ·
      refine ⟨10486676595915450944383229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6991117730610300629588819 10486676595915450944383229)
      ·
        refine ⟨3932503723468294104143711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10486676595915450944383229 3932503723468294104143711)
        ·
          refine ⟨5898755585202441156215567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3932503723468294104143711 5898755585202441156215567)
          ·
            refine ⟨8848133377803661734323351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5898755585202441156215567 8848133377803661734323351)
            ·
              refine ⟨13272200066705492601485027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8848133377803661734323351 13272200066705492601485027)
              ·
                refine ⟨19908300100058238902227541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13272200066705492601485027 19908300100058238902227541)
                ·
                  refine ⟨233300391797557487135479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19908300100058238902227541 233300391797557487135479)
                  ·
                    rfl

theorem cell23_4089158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_4089158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089158 prefixEnd_4089158 := by exact prefixLift 4089158
  have htrace : WordTrace (prefixWord ++ tailWord_4089158) baseStart_4089158 baseEnd_4089158 := by
    simpa [prefixWord, tailWord_4089158, baseEnd_4089158] using wordTrace_append hprefix tailTrace_4089158
  have hstable : (prefixWord ++ tailWord_4089158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089158).length < 2 ^ (prefixWord ++ tailWord_4089158).sum := by decide
  have hdescent : baseEnd_4089158 < baseStart_4089158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089177 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 5]
def baseStart_4089177 : Nat := 118140960795 + 4089177 * 2 ^ 59
def prefixEnd_4089177 : Nat := 4983230072969 + 3 ^ 40 * 4089177 * 2
def baseEnd_4089177 : Nat := 2099713282310452809881723

theorem tailTrace_4089177 : CollatzResearch.WordTrace tailWord_4089177 prefixEnd_4089177 2099713282310452809881723 := by
  unfold tailWord_4089177
  simp only [CollatzResearch.WordTrace]
  refine ⟨149144537906617579676169785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99429691937745053117446523 149144537906617579676169785)
  ·
    refine ⟨111858403429963184757127339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149144537906617579676169785 111858403429963184757127339)
    ·
      refine ⟨167787605144944777135691009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111858403429963184757127339 167787605144944777135691009)
      ·
        refine ⟨125840703858708582851768257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167787605144944777135691009 125840703858708582851768257)
        ·
          refine ⟨94380527894031437138826193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125840703858708582851768257 94380527894031437138826193)
          ·
            refine ⟨70785395920523577854119645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94380527894031437138826193 70785395920523577854119645)
            ·
              refine ⟨26544523470196341695294867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70785395920523577854119645 26544523470196341695294867)
              ·
                refine ⟨39816785205294512542942301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26544523470196341695294867 39816785205294512542942301)
                ·
                  refine ⟨14931294451985442203603363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39816785205294512542942301 14931294451985442203603363)
                  ·
                    refine ⟨22396941677978163305405045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14931294451985442203603363 22396941677978163305405045)
                    ·
                      refine ⟨2099713282310452809881723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22396941677978163305405045 2099713282310452809881723)
                      ·
                        rfl

theorem cell23_4089177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_4089177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089177 prefixEnd_4089177 := by exact prefixLift 4089177
  have htrace : WordTrace (prefixWord ++ tailWord_4089177) baseStart_4089177 baseEnd_4089177 := by
    simpa [prefixWord, tailWord_4089177, baseEnd_4089177] using wordTrace_append hprefix tailTrace_4089177
  have hstable : (prefixWord ++ tailWord_4089177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089177).length < 2 ^ (prefixWord ++ tailWord_4089177).sum := by decide
  have hdescent : baseEnd_4089177 < baseStart_4089177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089184 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 1, 6]
def baseStart_4089184 : Nat := 118140960795 + 4089184 * 2 ^ 59
def prefixEnd_4089184 : Nat := 4983230072969 + 3 ^ 40 * 4089184 * 2
def baseEnd_4089184 : Nat := 699905625558344760831397

theorem tailTrace_4089184 : CollatzResearch.WordTrace tailWord_4089184 prefixEnd_4089184 699905625558344760831397 := by
  unfold tailWord_4089184
  simp only [CollatzResearch.WordTrace]
  refine ⟨74572396608796109935837303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99429862145061479914449737 74572396608796109935837303)
  ·
    refine ⟨111858594913194164903755955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74572396608796109935837303 111858594913194164903755955)
    ·
      refine ⟨167787892369791247355633933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111858594913194164903755955 167787892369791247355633933)
      ·
        refine ⟨62920459638671717758362725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167787892369791247355633933 62920459638671717758362725)
        ·
          refine ⟨11797586182250947079693011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62920459638671717758362725 11797586182250947079693011)
          ·
            refine ⟨17696379273376420619539517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11797586182250947079693011 17696379273376420619539517)
            ·
              refine ⟨6636142227516157732327319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17696379273376420619539517 6636142227516157732327319)
              ·
                refine ⟨9954213341274236598490979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636142227516157732327319 9954213341274236598490979)
                ·
                  refine ⟨14931320011911354897736469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9954213341274236598490979 14931320011911354897736469)
                  ·
                    refine ⟨699905625558344760831397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14931320011911354897736469 699905625558344760831397)
                    ·
                      rfl

theorem cell23_4089184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 6].length) (baseStart_4089184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089184 prefixEnd_4089184 := by exact prefixLift 4089184
  have htrace : WordTrace (prefixWord ++ tailWord_4089184) baseStart_4089184 baseEnd_4089184 := by
    simpa [prefixWord, tailWord_4089184, baseEnd_4089184] using wordTrace_append hprefix tailTrace_4089184
  have hstable : (prefixWord ++ tailWord_4089184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089184).length < 2 ^ (prefixWord ++ tailWord_4089184).sum := by decide
  have hdescent : baseEnd_4089184 < baseStart_4089184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089218 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4089218 : Nat := 118140960795 + 4089218 * 2 ^ 59
def prefixEnd_4089218 : Nat := 4983230072969 + 3 ^ 40 * 4089218 * 2
def baseEnd_4089218 : Nat := 699911445005762383156345

theorem tailTrace_4089218 : CollatzResearch.WordTrace tailWord_4089218 prefixEnd_4089218 699911445005762383156345 := by
  unfold tailWord_4089218
  simp only [CollatzResearch.WordTrace]
  refine ⟨37286508324867260919603077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99430688866312695785608205 37286508324867260919603077)
  ·
    refine ⟨6991220310912611422425577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37286508324867260919603077 6991220310912611422425577)
    ·
      refine ⟨5243415233184458566819183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6991220310912611422425577 5243415233184458566819183)
      ·
        refine ⟨7865122849776687850228775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243415233184458566819183 7865122849776687850228775)
        ·
          refine ⟨11797684274665031775343163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7865122849776687850228775 11797684274665031775343163)
          ·
            refine ⟨17696526411997547663014745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11797684274665031775343163 17696526411997547663014745)
            ·
              refine ⟨13272394808998160747261059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17696526411997547663014745 13272394808998160747261059)
              ·
                refine ⟨19908592213497241120891589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13272394808998160747261059 19908592213497241120891589)
                ·
                  refine ⟨3732861040030732710167173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19908592213497241120891589 3732861040030732710167173)
                  ·
                    refine ⟨699911445005762383156345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3732861040030732710167173 699911445005762383156345)
                    ·
                      rfl

theorem cell23_4089218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4089218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089218 prefixEnd_4089218 := by exact prefixLift 4089218
  have htrace : WordTrace (prefixWord ++ tailWord_4089218) baseStart_4089218 baseEnd_4089218 := by
    simpa [prefixWord, tailWord_4089218, baseEnd_4089218] using wordTrace_append hprefix tailTrace_4089218
  have hstable : (prefixWord ++ tailWord_4089218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089218).length < 2 ^ (prefixWord ++ tailWord_4089218).sum := by decide
  have hdescent : baseEnd_4089218 < baseStart_4089218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089225 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 3, 2, 2]
def baseStart_4089225 : Nat := 118140960795 + 4089225 * 2 ^ 59
def prefixEnd_4089225 : Nat := 4983230072969 + 3 ^ 40 * 4089225 * 2
def baseEnd_4089225 : Nat := 2099737929381868622081503

theorem tailTrace_4089225 : CollatzResearch.WordTrace tailWord_4089225 prefixEnd_4089225 2099737929381868622081503 := by
  unfold tailWord_4089225
  simp only [CollatzResearch.WordTrace]
  refine ⟨149146288610443683873917129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99430859073629122582611419 149146288610443683873917129)
  ·
    refine ⟨111859716457832762905437847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149146288610443683873917129 111859716457832762905437847)
    ·
      refine ⟨167789574686749144358156771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111859716457832762905437847 167789574686749144358156771)
      ·
        refine ⟨251684362030123716537235157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167789574686749144358156771 251684362030123716537235157)
        ·
          refine ⟨5898852235081024606341449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 251684362030123716537235157 5898852235081024606341449)
          ·
            refine ⟨4424139176310768454756087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5898852235081024606341449 4424139176310768454756087)
            ·
              refine ⟨6636208764466152682134131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424139176310768454756087 6636208764466152682134131)
              ·
                refine ⟨9954313146699229023201197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636208764466152682134131 9954313146699229023201197)
                ·
                  refine ⟨3732867430012210883700449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9954313146699229023201197 3732867430012210883700449)
                  ·
                    refine ⟨2799650572509158162775337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3732867430012210883700449 2799650572509158162775337)
                    ·
                      refine ⟨2099737929381868622081503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799650572509158162775337 2099737929381868622081503)
                      ·
                        rfl

theorem cell23_4089225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 2, 2].length) (baseStart_4089225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089225 prefixEnd_4089225 := by exact prefixLift 4089225
  have htrace : WordTrace (prefixWord ++ tailWord_4089225) baseStart_4089225 baseEnd_4089225 := by
    simpa [prefixWord, tailWord_4089225, baseEnd_4089225] using wordTrace_append hprefix tailTrace_4089225
  have hstable : (prefixWord ++ tailWord_4089225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089225).length < 2 ^ (prefixWord ++ tailWord_4089225).sum := by decide
  have hdescent : baseEnd_4089225 < baseStart_4089225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089227 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 2, 7]
def baseStart_4089227 : Nat := 118140960795 + 4089227 * 2 ^ 59
def prefixEnd_4089227 : Nat := 4983230072969 + 3 ^ 40 * 4089227 * 2
def baseEnd_4089227 : Nat := 699912985447725871418831

theorem tailTrace_4089227 : CollatzResearch.WordTrace tailWord_4089227 prefixEnd_4089227 699912985447725871418831 := by
  unfold tailWord_4089227
  simp only [CollatzResearch.WordTrace]
  refine ⟨149146361556436438215489935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99430907704290958810326623 149146361556436438215489935)
  ·
    refine ⟨223719542334654657323234903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149146361556436438215489935 223719542334654657323234903)
    ·
      refine ⟨335579313501981985984852355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223719542334654657323234903 335579313501981985984852355)
      ·
        refine ⟨503368970252972978977278533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335579313501981985984852355 503368970252972978977278533)
        ·
          refine ⟨94381681922432433558239725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503368970252972978977278533 94381681922432433558239725)
          ·
            refine ⟨35393130720912162584339897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94381681922432433558239725 35393130720912162584339897)
            ·
              refine ⟨26544848040684121938254923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35393130720912162584339897 26544848040684121938254923)
              ·
                refine ⟨39817272061026182907382385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26544848040684121938254923 39817272061026182907382385)
                ·
                  refine ⟨29862954045769637180536789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39817272061026182907382385 29862954045769637180536789)
                  ·
                    refine ⟨699912985447725871418831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29862954045769637180536789 699912985447725871418831)
                    ·
                      rfl

theorem cell23_4089227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 7].length) (baseStart_4089227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089227 prefixEnd_4089227 := by exact prefixLift 4089227
  have htrace : WordTrace (prefixWord ++ tailWord_4089227) baseStart_4089227 baseEnd_4089227 := by
    simpa [prefixWord, tailWord_4089227, baseEnd_4089227] using wordTrace_append hprefix tailTrace_4089227
  have hstable : (prefixWord ++ tailWord_4089227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089227).length < 2 ^ (prefixWord ++ tailWord_4089227).sum := by decide
  have hdescent : baseEnd_4089227 < baseStart_4089227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089251 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 3, 3, 2]
def baseStart_4089251 : Nat := 118140960795 + 4089251 * 2 ^ 59
def prefixEnd_4089251 : Nat := 4983230072969 + 3 ^ 40 * 4089251 * 2
def baseEnd_4089251 : Nat := 2099751279878885520356383

theorem tailTrace_4089251 : CollatzResearch.WordTrace tailWord_4089251 prefixEnd_4089251 2099751279878885520356383 := by
  unfold tailWord_4089251
  simp only [CollatzResearch.WordTrace]
  refine ⟨149147236908349490314363607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99431491272232993542909071 149147236908349490314363607)
  ·
    refine ⟨223720855362524235471545411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149147236908349490314363607 223720855362524235471545411)
    ·
      refine ⟨335581283043786353207318117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223720855362524235471545411 335581283043786353207318117)
      ·
        refine ⟨62921490570709941226372147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335581283043786353207318117 62921490570709941226372147)
        ·
          refine ⟨94382235856064911839558221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62921490570709941226372147 94382235856064911839558221)
          ·
            refine ⟨35393338446024341939834333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94382235856064911839558221 35393338446024341939834333)
            ·
              refine ⟨13272501917259128227437875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35393338446024341939834333 13272501917259128227437875)
              ·
                refine ⟨19908752875888692341156813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13272501917259128227437875 19908752875888692341156813)
                ·
                  refine ⟨7465782328458259627933805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19908752875888692341156813 7465782328458259627933805)
                  ·
                    refine ⟨2799668373171847360475177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7465782328458259627933805 2799668373171847360475177)
                    ·
                      refine ⟨2099751279878885520356383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799668373171847360475177 2099751279878885520356383)
                      ·
                        rfl

theorem cell23_4089251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_4089251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089251 prefixEnd_4089251 := by exact prefixLift 4089251
  have htrace : WordTrace (prefixWord ++ tailWord_4089251) baseStart_4089251 baseEnd_4089251 := by
    simpa [prefixWord, tailWord_4089251, baseEnd_4089251] using wordTrace_append hprefix tailTrace_4089251
  have hstable : (prefixWord ++ tailWord_4089251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089251).length < 2 ^ (prefixWord ++ tailWord_4089251).sum := by decide
  have hdescent : baseEnd_4089251 < baseStart_4089251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089257 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 6, 6]
def baseStart_4089257 : Nat := 118140960795 + 4089257 * 2 ^ 59
def prefixEnd_4089257 : Nat := 4983230072969 + 3 ^ 40 * 4089257 * 2
def baseEnd_4089257 : Nat := 699918120254270832293785

theorem tailTrace_4089257 : CollatzResearch.WordTrace tailWord_4089257 prefixEnd_4089257 699918120254270832293785 := by
  unfold tailWord_4089257
  simp only [CollatzResearch.WordTrace]
  refine ⟨149147455746327753339082025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99431637164218502226054683 149147455746327753339082025)
  ·
    refine ⟨111860591809745815004311519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149147455746327753339082025 111860591809745815004311519)
    ·
      refine ⟨167790887714618722506467279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111860591809745815004311519 167790887714618722506467279)
      ·
        refine ⟨251686331571928083759700919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167790887714618722506467279 251686331571928083759700919)
        ·
          refine ⟨377529497357892125639551379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251686331571928083759700919 377529497357892125639551379)
          ·
            refine ⟨566294246036838188459327069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377529497357892125639551379 566294246036838188459327069)
            ·
              refine ⟨212360342263814320672247651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566294246036838188459327069 212360342263814320672247651)
              ·
                refine ⟨318540513395721481008371477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212360342263814320672247651 318540513395721481008371477)
                ·
                  refine ⟨14931586565424444422267413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 318540513395721481008371477 14931586565424444422267413)
                  ·
                    refine ⟨699918120254270832293785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14931586565424444422267413 699918120254270832293785)
                    ·
                      rfl

theorem cell23_4089257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_4089257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089257 prefixEnd_4089257 := by exact prefixLift 4089257
  have htrace : WordTrace (prefixWord ++ tailWord_4089257) baseStart_4089257 baseEnd_4089257 := by
    simpa [prefixWord, tailWord_4089257, baseEnd_4089257] using wordTrace_append hprefix tailTrace_4089257
  have hstable : (prefixWord ++ tailWord_4089257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089257).length < 2 ^ (prefixWord ++ tailWord_4089257).sum := by decide
  have hdescent : baseEnd_4089257 < baseStart_4089257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089276 : List Nat := [2, 2, 2, 4, 3, 1, 2, 2, 1, 2, 2]
def baseStart_4089276 : Nat := 118140960795 + 4089276 * 2 ^ 59
def prefixEnd_4089276 : Nat := 4983230072969 + 3 ^ 40 * 4089276 * 2
def baseEnd_4089276 : Nat := 2099764116895247922543769

theorem tailTrace_4089276 : CollatzResearch.WordTrace tailWord_4089276 prefixEnd_4089276 2099764116895247922543769 := by
  unfold tailWord_4089276
  simp only [CollatzResearch.WordTrace]
  refine ⟨74574074366629459792011841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99432099155505946389349121 74574074366629459792011841)
  ·
    refine ⟨55930555774972094844008881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74574074366629459792011841 55930555774972094844008881)
    ·
      refine ⟨41947916831229071133006661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55930555774972094844008881 41947916831229071133006661)
      ·
        refine ⟨7865234405855450837438749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41947916831229071133006661 7865234405855450837438749)
        ·
          refine ⟨2949462902195794064039531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7865234405855450837438749 2949462902195794064039531)
          ·
            refine ⟨4424194353293691096059297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949462902195794064039531 4424194353293691096059297)
            ·
              refine ⟨3318145764970268322044473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4424194353293691096059297 3318145764970268322044473)
              ·
                refine ⟨2488609323727701241533355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3318145764970268322044473 2488609323727701241533355)
                ·
                  refine ⟨3732913985591551862300033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488609323727701241533355 3732913985591551862300033)
                  ·
                    refine ⟨2799685489193663896725025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3732913985591551862300033 2799685489193663896725025)
                    ·
                      refine ⟨2099764116895247922543769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799685489193663896725025 2099764116895247922543769)
                      ·
                        rfl

theorem cell23_4089276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_4089276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089276 prefixEnd_4089276 := by exact prefixLift 4089276
  have htrace : WordTrace (prefixWord ++ tailWord_4089276) baseStart_4089276 baseEnd_4089276 := by
    simpa [prefixWord, tailWord_4089276, baseEnd_4089276] using wordTrace_append hprefix tailTrace_4089276
  have hstable : (prefixWord ++ tailWord_4089276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089276).length < 2 ^ (prefixWord ++ tailWord_4089276).sum := by decide
  have hdescent : baseEnd_4089276 < baseStart_4089276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089282 : List Nat := [3, 5, 2, 1, 1, 2, 1, 8]
def baseStart_4089282 : Nat := 118140960795 + 4089282 * 2 ^ 59
def prefixEnd_4089282 : Nat := 4983230072969 + 3 ^ 40 * 4089282 * 2
def baseEnd_4089282 : Nat := 77769155473302774039583

theorem tailTrace_4089282 : CollatzResearch.WordTrace tailWord_4089282 prefixEnd_4089282 77769155473302774039583 := by
  unfold tailWord_4089282
  simp only [CollatzResearch.WordTrace]
  refine ⟨37287091892809295652185525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99432245047491455072494733 37287091892809295652185525)
  ·
    refine ⟨3495664864950871467392393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37287091892809295652185525 3495664864950871467392393)
    ·
      refine ⟨2621748648713153600544295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3495664864950871467392393 2621748648713153600544295)
      ·
        refine ⟨3932622973069730400816443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2621748648713153600544295 3932622973069730400816443)
        ·
          refine ⟨5898934459604595601224665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3932622973069730400816443 5898934459604595601224665)
          ·
            refine ⟨4424200844703446700918499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5898934459604595601224665 4424200844703446700918499)
            ·
              refine ⟨6636301267055170051377749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424200844703446700918499 6636301267055170051377749)
              ·
                refine ⟨77769155473302774039583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6636301267055170051377749 77769155473302774039583)
                ·
                  rfl

theorem cell23_4089282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 8].length) (baseStart_4089282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089282 prefixEnd_4089282 := by exact prefixLift 4089282
  have htrace : WordTrace (prefixWord ++ tailWord_4089282) baseStart_4089282 baseEnd_4089282 := by
    simpa [prefixWord, tailWord_4089282, baseEnd_4089282] using wordTrace_append hprefix tailTrace_4089282
  have hstable : (prefixWord ++ tailWord_4089282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089282).length < 2 ^ (prefixWord ++ tailWord_4089282).sum := by decide
  have hdescent : baseEnd_4089282 < baseStart_4089282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089294 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_4089294 : Nat := 118140960795 + 4089294 * 2 ^ 59
def prefixEnd_4089294 : Nat := 4983230072969 + 3 ^ 40 * 4089294 * 2
def baseEnd_4089294 : Nat := 2099773359547028852118685

theorem tailTrace_4089294 : CollatzResearch.WordTrace tailWord_4089294 prefixEnd_4089294 2099773359547028852118685 := by
  unfold tailWord_4089294
  simp only [CollatzResearch.WordTrace]
  refine ⟨18643600655899213582272367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99432536831462472438785957 18643600655899213582272367)
  ·
    refine ⟨27965400983848820373408551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18643600655899213582272367 27965400983848820373408551)
    ·
      refine ⟨41948101475773230560112827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27965400983848820373408551 41948101475773230560112827)
      ·
        refine ⟨62922152213659845840169241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41948101475773230560112827 62922152213659845840169241)
        ·
          refine ⟨47191614160244884380126931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62922152213659845840169241 47191614160244884380126931)
          ·
            refine ⟨70787421240367326570190397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47191614160244884380126931 70787421240367326570190397)
            ·
              refine ⟨26545282965137747463821399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70787421240367326570190397 26545282965137747463821399)
              ·
                refine ⟨39817924447706621195732099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26545282965137747463821399 39817924447706621195732099)
                ·
                  refine ⟨59726886671559931793598149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39817924447706621195732099 59726886671559931793598149)
                  ·
                    refine ⟨11198791250917487211299653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59726886671559931793598149 11198791250917487211299653)
                    ·
                      refine ⟨2099773359547028852118685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11198791250917487211299653 2099773359547028852118685)
                      ·
                        rfl

theorem cell23_4089294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_4089294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089294 prefixEnd_4089294 := by exact prefixLift 4089294
  have htrace : WordTrace (prefixWord ++ tailWord_4089294) baseStart_4089294 baseEnd_4089294 := by
    simpa [prefixWord, tailWord_4089294, baseEnd_4089294] using wordTrace_append hprefix tailTrace_4089294
  have hstable : (prefixWord ++ tailWord_4089294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089294).length < 2 ^ (prefixWord ++ tailWord_4089294).sum := by decide
  have hdescent : baseEnd_4089294 < baseStart_4089294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089307 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 8]
def baseStart_4089307 : Nat := 118140960795 + 4089307 * 2 ^ 59
def prefixEnd_4089307 : Nat := 4983230072969 + 3 ^ 40 * 4089307 * 2
def baseEnd_4089307 : Nat := 2099780034795537301256125

theorem tailTrace_4089307 : CollatzResearch.WordTrace tailWord_4089307 prefixEnd_4089307 2099780034795537301256125 := by
  unfold tailWord_4089307
  simp only [CollatzResearch.WordTrace]
  refine ⟨149149279396146611878402175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99432852930764407918934783 149149279396146611878402175)
  ·
    refine ⟨223723919094219917817603263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149149279396146611878402175 223723919094219917817603263)
    ·
      refine ⟨335585878641329876726404895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223723919094219917817603263 335585878641329876726404895)
      ·
        refine ⟨503378817961994815089607343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335585878641329876726404895 503378817961994815089607343)
        ·
          refine ⟨755068226942992222634411015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503378817961994815089607343 755068226942992222634411015)
          ·
            refine ⟨1132602340414488333951616523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755068226942992222634411015 1132602340414488333951616523)
            ·
              refine ⟨1698903510621732500927424785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132602340414488333951616523 1698903510621732500927424785)
              ·
                refine ⟨1274177632966299375695568589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698903510621732500927424785 1274177632966299375695568589)
                ·
                  refine ⟨477816612362362265885838221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274177632966299375695568589 477816612362362265885838221)
                  ·
                    refine ⟨179181229635885849707189333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 477816612362362265885838221 179181229635885849707189333)
                    ·
                      refine ⟨2099780034795537301256125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 179181229635885849707189333 2099780034795537301256125)
                      ·
                        rfl

theorem cell23_4089307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_4089307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089307 prefixEnd_4089307 := by exact prefixLift 4089307
  have htrace : WordTrace (prefixWord ++ tailWord_4089307) baseStart_4089307 baseEnd_4089307 := by
    simpa [prefixWord, tailWord_4089307, baseEnd_4089307] using wordTrace_append hprefix tailTrace_4089307
  have hstable : (prefixWord ++ tailWord_4089307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089307).length < 2 ^ (prefixWord ++ tailWord_4089307).sum := by decide
  have hdescent : baseEnd_4089307 < baseStart_4089307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089434 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_4089434 : Nat := 118140960795 + 4089434 * 2 ^ 59
def prefixEnd_4089434 : Nat := 4983230072969 + 3 ^ 40 * 4089434 * 2
def baseEnd_4089434 : Nat := 2099845246838658304368041

theorem tailTrace_4089434 : CollatzResearch.WordTrace tailWord_4089434 prefixEnd_4089434 2099845246838658304368041 := by
  unfold tailWord_4089434
  simp only [CollatzResearch.WordTrace]
  refine ⟨37288477866671628142068839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99435940977791008378850237 37288477866671628142068839)
  ·
    refine ⟨55932716800007442213103259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37288477866671628142068839 55932716800007442213103259)
    ·
      refine ⟨83899075200011163319654889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55932716800007442213103259 83899075200011163319654889)
      ·
        refine ⟨62924306400008372489741167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83899075200011163319654889 62924306400008372489741167)
        ·
          refine ⟨94386459600012558734611751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62924306400008372489741167 94386459600012558734611751)
          ·
            refine ⟨141579689400018838101917627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94386459600012558734611751 141579689400018838101917627)
            ·
              refine ⟨212369534100028257152876441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141579689400018838101917627 212369534100028257152876441)
              ·
                refine ⟨159277150575021192864657331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212369534100028257152876441 159277150575021192864657331)
                ·
                  refine ⟨238915725862531789296985997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159277150575021192864657331 238915725862531789296985997)
                  ·
                    refine ⟨89593397198449420986369749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238915725862531789296985997 89593397198449420986369749)
                    ·
                      refine ⟨2099845246838658304368041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89593397198449420986369749 2099845246838658304368041)
                      ·
                        rfl

theorem cell23_4089434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_4089434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089434 prefixEnd_4089434 := by exact prefixLift 4089434
  have htrace : WordTrace (prefixWord ++ tailWord_4089434) baseStart_4089434 baseEnd_4089434 := by
    simpa [prefixWord, tailWord_4089434, baseEnd_4089434] using wordTrace_append hprefix tailTrace_4089434
  have hstable : (prefixWord ++ tailWord_4089434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089434).length < 2 ^ (prefixWord ++ tailWord_4089434).sum := by decide
  have hdescent : baseEnd_4089434 < baseStart_4089434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089482 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2]
def baseStart_4089482 : Nat := 118140960795 + 4089482 * 2 ^ 59
def prefixEnd_4089482 : Nat := 4983230072969 + 3 ^ 40 * 4089482 * 2
def baseEnd_4089482 : Nat := 2099869893910074116567821

theorem tailTrace_4089482 : CollatzResearch.WordTrace tailWord_4089482 prefixEnd_4089482 2099869893910074116567821 := by
  unfold tailWord_4089482
  simp only [CollatzResearch.WordTrace]
  refine ⟨37288915542628154191505675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99437108113675077844015133 37288915542628154191505675)
  ·
    refine ⟨55933373313942231287258513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37288915542628154191505675 55933373313942231287258513)
    ·
      refine ⟨41950029985456673465443885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55933373313942231287258513 41950029985456673465443885)
      ·
        refine ⟨15731261244546252549541457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41950029985456673465443885 15731261244546252549541457)
        ·
          refine ⟨11798445933409689412156093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15731261244546252549541457 11798445933409689412156093)
          ·
            refine ⟨4424417225028633529558535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11798445933409689412156093 4424417225028633529558535)
            ·
              refine ⟨6636625837542950294337803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424417225028633529558535 6636625837542950294337803)
              ·
                refine ⟨9954938756314425441506705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636625837542950294337803 9954938756314425441506705)
                ·
                  refine ⟨7466204067235819081130029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9954938756314425441506705 7466204067235819081130029)
                  ·
                    refine ⟨2799826525213432155423761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7466204067235819081130029 2799826525213432155423761)
                    ·
                      refine ⟨2099869893910074116567821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799826525213432155423761 2099869893910074116567821)
                      ·
                        rfl

theorem cell23_4089482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_4089482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089482 prefixEnd_4089482 := by exact prefixLift 4089482
  have htrace : WordTrace (prefixWord ++ tailWord_4089482) baseStart_4089482 baseEnd_4089482 := by
    simpa [prefixWord, tailWord_4089482, baseEnd_4089482] using wordTrace_append hprefix tailTrace_4089482
  have hstable : (prefixWord ++ tailWord_4089482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089482).length < 2 ^ (prefixWord ++ tailWord_4089482).sum := by decide
  have hdescent : baseEnd_4089482 < baseStart_4089482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089495 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 1, 1, 4]
def baseStart_4089495 : Nat := 118140960795 + 4089495 * 2 ^ 59
def prefixEnd_4089495 : Nat := 4983230072969 + 3 ^ 40 * 4089495 * 2
def baseEnd_4089495 : Nat := 2099876569158582565705261

theorem tailTrace_4089495 : CollatzResearch.WordTrace tailWord_4089495 prefixEnd_4089495 2099876569158582565705261 := by
  unfold tailWord_4089495
  simp only [CollatzResearch.WordTrace]
  refine ⟨149156136319465519986245939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99437424212977013324163959 149156136319465519986245939)
  ·
    refine ⟨223734204479198279979368909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149156136319465519986245939 223734204479198279979368909)
    ·
      refine ⟨83900326679699354992263341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223734204479198279979368909 83900326679699354992263341)
      ·
        refine ⟨31462622504887258122098753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83900326679699354992263341 31462622504887258122098753)
        ·
          refine ⟨23596966878665443591574065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31462622504887258122098753 23596966878665443591574065)
          ·
            refine ⟨17697725158999082693680549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23596966878665443591574065 17697725158999082693680549)
            ·
              refine ⟨3318323467312328005065103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17697725158999082693680549 3318323467312328005065103)
              ·
                refine ⟨4977485200968492007597655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3318323467312328005065103 4977485200968492007597655)
                ·
                  refine ⟨7466227801452738011396483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4977485200968492007597655 7466227801452738011396483)
                  ·
                    refine ⟨11199341702179107017094725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7466227801452738011396483 11199341702179107017094725)
                    ·
                      refine ⟨2099876569158582565705261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11199341702179107017094725 2099876569158582565705261)
                      ·
                        rfl

theorem cell23_4089495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_4089495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089495 prefixEnd_4089495 := by exact prefixLift 4089495
  have htrace : WordTrace (prefixWord ++ tailWord_4089495) baseStart_4089495 baseEnd_4089495 := by
    simpa [prefixWord, tailWord_4089495, baseEnd_4089495] using wordTrace_append hprefix tailTrace_4089495
  have hstable : (prefixWord ++ tailWord_4089495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089495).length < 2 ^ (prefixWord ++ tailWord_4089495).sum := by decide
  have hdescent : baseEnd_4089495 < baseStart_4089495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089505 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 2, 4]
def baseStart_4089505 : Nat := 118140960795 + 4089505 * 2 ^ 59
def prefixEnd_4089505 : Nat := 4983230072969 + 3 ^ 40 * 4089505 * 2
def baseEnd_4089505 : Nat := 699960567988375842193405

theorem tailTrace_4089505 : CollatzResearch.WordTrace tailWord_4089505 prefixEnd_4089505 699960567988375842193405 := by
  unfold tailWord_4089505
  simp only [CollatzResearch.WordTrace]
  refine ⟨149156501049429291694109969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99437667366286194462739979 149156501049429291694109969)
  ·
    refine ⟨111867375787071968770582477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149156501049429291694109969 111867375787071968770582477)
    ·
      refine ⟨41950265920151988288968429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111867375787071968770582477 41950265920151988288968429)
      ·
        refine ⟨15731349720056995608363161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41950265920151988288968429 15731349720056995608363161)
        ·
          refine ⟨11798512290042746706272371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15731349720056995608363161 11798512290042746706272371)
          ·
            refine ⟨17697768435064120059408557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11798512290042746706272371 17697768435064120059408557)
            ·
              refine ⟨6636663163149045022278209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17697768435064120059408557 6636663163149045022278209)
              ·
                refine ⟨4977497372361783766708657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6636663163149045022278209 4977497372361783766708657)
                ·
                  refine ⟨3733123029271337825031493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4977497372361783766708657 3733123029271337825031493)
                  ·
                    refine ⟨699960567988375842193405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3733123029271337825031493 699960567988375842193405)
                    ·
                      rfl

theorem cell23_4089505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_4089505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089505 prefixEnd_4089505 := by exact prefixLift 4089505
  have htrace : WordTrace (prefixWord ++ tailWord_4089505) baseStart_4089505 baseEnd_4089505 := by
    simpa [prefixWord, tailWord_4089505, baseEnd_4089505] using wordTrace_append hprefix tailTrace_4089505
  have hstable : (prefixWord ++ tailWord_4089505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089505).length < 2 ^ (prefixWord ++ tailWord_4089505).sum := by decide
  have hdescent : baseEnd_4089505 < baseStart_4089505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089546 : List Nat := [3, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2]
def baseStart_4089546 : Nat := 118140960795 + 4089546 * 2 ^ 59
def prefixEnd_4089546 : Nat := 4983230072969 + 3 ^ 40 * 4089546 * 2
def baseEnd_4089546 : Nat := 2099902756671961866167527

theorem tailTrace_4089546 : CollatzResearch.WordTrace tailWord_4089546 prefixEnd_4089546 2099902756671961866167527 := by
  unfold tailWord_4089546
  simp only [CollatzResearch.WordTrace]
  refine ⟨37289499110570188924088123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99438664294853837130901661 37289499110570188924088123)
  ·
    refine ⟨55934248665855283386132185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37289499110570188924088123 55934248665855283386132185)
    ·
      refine ⟨41950686499391462539599139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55934248665855283386132185 41950686499391462539599139)
      ·
        refine ⟨62926029749087193809398709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41950686499391462539599139 62926029749087193809398709)
        ·
          refine ⟨5899315288976924419631129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62926029749087193809398709 5899315288976924419631129)
          ·
            refine ⟨4424486466732693314723347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5899315288976924419631129 4424486466732693314723347)
            ·
              refine ⟨6636729700099039972085021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424486466732693314723347 6636729700099039972085021)
              ·
                refine ⟨2488773637537139989531883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6636729700099039972085021 2488773637537139989531883)
                ·
                  refine ⟨3733160456305709984297825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488773637537139989531883 3733160456305709984297825)
                  ·
                    refine ⟨2799870342229282488223369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3733160456305709984297825 2799870342229282488223369)
                    ·
                      refine ⟨2099902756671961866167527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799870342229282488223369 2099902756671961866167527)
                      ·
                        rfl

theorem cell23_4089546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_4089546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089546 prefixEnd_4089546 := by exact prefixLift 4089546
  have htrace : WordTrace (prefixWord ++ tailWord_4089546) baseStart_4089546 baseEnd_4089546 := by
    simpa [prefixWord, tailWord_4089546, baseEnd_4089546] using wordTrace_append hprefix tailTrace_4089546
  have hstable : (prefixWord ++ tailWord_4089546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089546).length < 2 ^ (prefixWord ++ tailWord_4089546).sum := by decide
  have hdescent : baseEnd_4089546 < baseStart_4089546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089591 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 7]
def baseStart_4089591 : Nat := 118140960795 + 4089591 * 2 ^ 59
def prefixEnd_4089591 : Nat := 4983230072969 + 3 ^ 40 * 4089591 * 2
def baseEnd_4089591 : Nat := 233325095922379354456091

theorem tailTrace_4089591 : CollatzResearch.WordTrace tailWord_4089591 prefixEnd_4089591 233325095922379354456091 := by
  unfold tailWord_4089591
  simp only [CollatzResearch.WordTrace]
  refine ⟨149159637727117728381740627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99439758484745152254493751 149159637727117728381740627)
  ·
    refine ⟨223739456590676592572610941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149159637727117728381740627 223739456590676592572610941)
    ·
      refine ⟨83902296221503722214729103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223739456590676592572610941 83902296221503722214729103)
      ·
        refine ⟨125853444332255583322093655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83902296221503722214729103 125853444332255583322093655)
        ·
          refine ⟨188780166498383374983140483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125853444332255583322093655 188780166498383374983140483)
          ·
            refine ⟨283170249747575062474710725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188780166498383374983140483 283170249747575062474710725)
            ·
              refine ⟨53094421827670324214008261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283170249747575062474710725 53094421827670324214008261)
              ·
                refine ⟨9955204092688185790126549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53094421827670324214008261 9955204092688185790126549)
                ·
                  refine ⟨233325095922379354456091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9955204092688185790126549 233325095922379354456091)
                  ·
                    rfl

theorem cell23_4089591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 7].length) (baseStart_4089591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089591 prefixEnd_4089591 := by exact prefixLift 4089591
  have htrace : WordTrace (prefixWord ++ tailWord_4089591) baseStart_4089591 baseEnd_4089591 := by
    simpa [prefixWord, tailWord_4089591, baseEnd_4089591] using wordTrace_append hprefix tailTrace_4089591
  have hstable : (prefixWord ++ tailWord_4089591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089591).length < 2 ^ (prefixWord ++ tailWord_4089591).sum := by decide
  have hdescent : baseEnd_4089591 < baseStart_4089591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089602 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_4089602 : Nat := 118140960795 + 4089602 * 2 ^ 59
def prefixEnd_4089602 : Nat := 4983230072969 + 3 ^ 40 * 4089602 * 2
def baseEnd_4089602 : Nat := 2099931511588613647067269

theorem tailTrace_4089602 : CollatzResearch.WordTrace tailWord_4089602 prefixEnd_4089602 2099931511588613647067269 := by
  unfold tailWord_4089602
  simp only [CollatzResearch.WordTrace]
  refine ⟨37290009732519469315097765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99440025953385251506927373 37290009732519469315097765)
  ·
    refine ⟨6991876824847400496580831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37290009732519469315097765 6991876824847400496580831)
    ·
      refine ⟨10487815237271100744871247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6991876824847400496580831 10487815237271100744871247)
      ·
        refine ⟨15731722855906651117306871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10487815237271100744871247 15731722855906651117306871)
        ·
          refine ⟨23597584283859976675960307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15731722855906651117306871 23597584283859976675960307)
          ·
            refine ⟨35396376425789965013940461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23597584283859976675960307 35396376425789965013940461)
            ·
              refine ⟨13273641159671236880227673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35396376425789965013940461 13273641159671236880227673)
              ·
                refine ⟨9955230869753427660170755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13273641159671236880227673 9955230869753427660170755)
                ·
                  refine ⟨14932846304630141490256133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9955230869753427660170755 14932846304630141490256133)
                  ·
                    refine ⟨2799908682118151529423025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14932846304630141490256133 2799908682118151529423025)
                    ·
                      refine ⟨2099931511588613647067269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2799908682118151529423025 2099931511588613647067269)
                      ·
                        rfl

theorem cell23_4089602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_4089602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089602 prefixEnd_4089602 := by exact prefixLift 4089602
  have htrace : WordTrace (prefixWord ++ tailWord_4089602) baseStart_4089602 baseEnd_4089602 := by
    simpa [prefixWord, tailWord_4089602, baseEnd_4089602] using wordTrace_append hprefix tailTrace_4089602
  have hstable : (prefixWord ++ tailWord_4089602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089602).length < 2 ^ (prefixWord ++ tailWord_4089602).sum := by decide
  have hdescent : baseEnd_4089602 < baseStart_4089602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089685 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 3, 4]
def baseStart_4089685 : Nat := 118140960795 + 4089685 * 2 ^ 59
def prefixEnd_4089685 : Nat := 4983230072969 + 3 ^ 40 * 4089685 * 2
def baseEnd_4089685 : Nat := 699991376827645607443129

theorem tailTrace_4089685 : CollatzResearch.WordTrace tailWord_4089685 prefixEnd_4089685 699991376827645607443129 := by
  unfold tailWord_4089685
  simp only [CollatzResearch.WordTrace]
  refine ⟨149163066188777182435662509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99442044125851454957108339 149163066188777182435662509)
  ·
    refine ⟨55936149820791443413373441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149163066188777182435662509 55936149820791443413373441)
    ·
      refine ⟨41952112365593582560030081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55936149820791443413373441 41952112365593582560030081)
      ·
        refine ⟨31464084274195186920022561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41952112365593582560030081 31464084274195186920022561)
        ·
          refine ⟨23598063205646390190016921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31464084274195186920022561 23598063205646390190016921)
          ·
            refine ⟨17698547404234792642512691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23598063205646390190016921 17698547404234792642512691)
            ·
              refine ⟨26547821106352188963769037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17698547404234792642512691 26547821106352188963769037)
              ·
                refine ⟨9955432914882070861413389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26547821106352188963769037 9955432914882070861413389)
                ·
                  refine ⟨3733287343080776573030021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9955432914882070861413389 3733287343080776573030021)
                  ·
                    refine ⟨699991376827645607443129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3733287343080776573030021 699991376827645607443129)
                    ·
                      rfl

theorem cell23_4089685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_4089685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089685 prefixEnd_4089685 := by exact prefixLift 4089685
  have htrace : WordTrace (prefixWord ++ tailWord_4089685) baseStart_4089685 baseEnd_4089685 := by
    simpa [prefixWord, tailWord_4089685, baseEnd_4089685] using wordTrace_append hprefix tailTrace_4089685
  have hstable : (prefixWord ++ tailWord_4089685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089685).length < 2 ^ (prefixWord ++ tailWord_4089685).sum := by decide
  have hdescent : baseEnd_4089685 < baseStart_4089685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089729 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_4089729 : Nat := 118140960795 + 4089729 * 2 ^ 59
def prefixEnd_4089729 : Nat := 4983230072969 + 3 ^ 40 * 4089729 * 2
def baseEnd_4089729 : Nat := 2099996723631734650179185

theorem tailTrace_4089729 : CollatzResearch.WordTrace tailWord_4089729 prefixEnd_4089729 2099996723631734650179185 := by
  unfold tailWord_4089729
  simp only [CollatzResearch.WordTrace]
  refine ⟨149164671000617777950264241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99443114000411851966842827 149164671000617777950264241)
  ·
    refine ⟨111873503250463333462698181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149164671000617777950264241 111873503250463333462698181)
    ·
      refine ⟨20976281859461875024255909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111873503250463333462698181 20976281859461875024255909)
      ·
        refine ⟨3933052848649101567047983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20976281859461875024255909 3933052848649101567047983)
        ·
          refine ⟨5899579272973652350571975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3933052848649101567047983 5899579272973652350571975)
          ·
            refine ⟨8849368909460478525857963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5899579272973652350571975 8849368909460478525857963)
            ·
              refine ⟨13274053364190717788786945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8849368909460478525857963 13274053364190717788786945)
              ·
                refine ⟨9955540023143038341590209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13274053364190717788786945 9955540023143038341590209)
                ·
                  refine ⟨7466655017357278756192657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9955540023143038341590209 7466655017357278756192657)
                  ·
                    refine ⟨5599991263017959067144493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7466655017357278756192657 5599991263017959067144493)
                    ·
                      refine ⟨2099996723631734650179185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5599991263017959067144493 2099996723631734650179185)
                      ·
                        rfl

theorem cell23_4089729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_4089729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089729 prefixEnd_4089729 := by exact prefixLift 4089729
  have htrace : WordTrace (prefixWord ++ tailWord_4089729) baseStart_4089729 baseEnd_4089729 := by
    simpa [prefixWord, tailWord_4089729, baseEnd_4089729] using wordTrace_append hprefix tailTrace_4089729
  have hstable : (prefixWord ++ tailWord_4089729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089729).length < 2 ^ (prefixWord ++ tailWord_4089729).sum := by decide
  have hdescent : baseEnd_4089729 < baseStart_4089729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089736 : List Nat := [2, 1, 3, 3, 3, 1, 3, 2, 1, 4]
def baseStart_4089736 : Nat := 118140960795 + 4089736 * 2 ^ 59
def prefixEnd_4089736 : Nat := 4983230072969 + 3 ^ 40 * 4089736 * 2
def baseEnd_4089736 : Nat := 700000105998772040930551

theorem tailTrace_4089736 : CollatzResearch.WordTrace tailWord_4089736 prefixEnd_4089736 700000105998772040930551 := by
  unfold tailWord_4089736
  simp only [CollatzResearch.WordTrace]
  refine ⟨74582463155796209072884531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99443284207728278763846041 74582463155796209072884531)
  ·
    refine ⟨111873694733694313609326797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74582463155796209072884531 111873694733694313609326797)
    ·
      refine ⟨41952635525135367603497549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111873694733694313609326797 41952635525135367603497549)
      ·
        refine ⟨15732238321925762851311581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41952635525135367603497549 15732238321925762851311581)
        ·
          refine ⟨5899589370722161069241843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15732238321925762851311581 5899589370722161069241843)
          ·
            refine ⟨8849384056083241603862765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5899589370722161069241843 8849384056083241603862765)
            ·
              refine ⟨3318519021031215601448537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8849384056083241603862765 3318519021031215601448537)
              ·
                refine ⟨2488889265773411701086403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3318519021031215601448537 2488889265773411701086403)
                ·
                  refine ⟨3733333898660117551629605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488889265773411701086403 3733333898660117551629605)
                  ·
                    refine ⟨700000105998772040930551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3733333898660117551629605 700000105998772040930551)
                    ·
                      rfl

theorem cell23_4089736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_4089736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089736 prefixEnd_4089736 := by exact prefixLift 4089736
  have htrace : WordTrace (prefixWord ++ tailWord_4089736) baseStart_4089736 baseEnd_4089736 := by
    simpa [prefixWord, tailWord_4089736, baseEnd_4089736] using wordTrace_append hprefix tailTrace_4089736
  have hstable : (prefixWord ++ tailWord_4089736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089736).length < 2 ^ (prefixWord ++ tailWord_4089736).sum := by decide
  have hdescent : baseEnd_4089736 < baseStart_4089736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089762 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_4089762 : Nat := 118140960795 + 4089762 * 2 ^ 59
def prefixEnd_4089762 : Nat := 4983230072969 + 3 ^ 40 * 4089762 * 2
def baseEnd_4089762 : Nat := 700004556164444340355511

theorem tailTrace_4089762 : CollatzResearch.WordTrace tailWord_4089762 prefixEnd_4089762 700004556164444340355511 := by
  unfold tailWord_4089762
  simp only [CollatzResearch.WordTrace]
  refine ⟨37291468652374556146553885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99443916406332149724143693 37291468652374556146553885)
  ·
    refine ⟨13984300744640458554957707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37291468652374556146553885 13984300744640458554957707)
    ·
      refine ⟨20976451116960687832436561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13984300744640458554957707 20976451116960687832436561)
      ·
        refine ⟨15732338337720515874327421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20976451116960687832436561 15732338337720515874327421)
        ·
          refine ⟨5899626876645193452872783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15732338337720515874327421 5899626876645193452872783)
          ·
            refine ⟨8849440314967790179309175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5899626876645193452872783 8849440314967790179309175)
            ·
              refine ⟨13274160472451685268963763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8849440314967790179309175 13274160472451685268963763)
              ·
                refine ⟨19911240708677527903445645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13274160472451685268963763 19911240708677527903445645)
                ·
                  refine ⟨7466715265754072963792117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19911240708677527903445645 7466715265754072963792117)
                  ·
                    refine ⟨700004556164444340355511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7466715265754072963792117 700004556164444340355511)
                    ·
                      rfl

theorem cell23_4089762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_4089762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089762 prefixEnd_4089762 := by exact prefixLift 4089762
  have htrace : WordTrace (prefixWord ++ tailWord_4089762) baseStart_4089762 baseEnd_4089762 := by
    simpa [prefixWord, tailWord_4089762, baseEnd_4089762] using wordTrace_append hprefix tailTrace_4089762
  have hstable : (prefixWord ++ tailWord_4089762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089762).length < 2 ^ (prefixWord ++ tailWord_4089762).sum := by decide
  have hdescent : baseEnd_4089762 < baseStart_4089762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089765 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 2, 6, 2]
def baseStart_4089765 : Nat := 118140960795 + 4089765 * 2 ^ 59
def prefixEnd_4089765 : Nat := 4983230072969 + 3 ^ 40 * 4089765 * 2
def baseEnd_4089765 : Nat := 2100015208935296509329019

theorem tailTrace_4089765 : CollatzResearch.WordTrace tailWord_4089765 prefixEnd_4089765 2100015208935296509329019 := by
  unfold tailWord_4089765
  simp only [CollatzResearch.WordTrace]
  refine ⟨149165984028487356098574749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99443989352324904065716499 149165984028487356098574749)
  ·
    refine ⟨55937244010682758536965531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149165984028487356098574749 55937244010682758536965531)
    ·
      refine ⟨83905866016024137805448297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55937244010682758536965531 83905866016024137805448297)
      ·
        refine ⟨62929399512018103354086223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83905866016024137805448297 62929399512018103354086223)
        ·
          refine ⟨94394099268027155031129335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62929399512018103354086223 94394099268027155031129335)
          ·
            refine ⟨141591148902040732546694003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94394099268027155031129335 141591148902040732546694003)
            ·
              refine ⟨212386723353061098820041005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141591148902040732546694003 212386723353061098820041005)
              ·
                refine ⟨79645021257397912057515377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212386723353061098820041005 79645021257397912057515377)
                ·
                  refine ⟨59733765943048434043136533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79645021257397912057515377 59733765943048434043136533)
                  ·
                    refine ⟨2800020278580395345772025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59733765943048434043136533 2800020278580395345772025)
                    ·
                      refine ⟨2100015208935296509329019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800020278580395345772025 2100015208935296509329019)
                      ·
                        rfl

theorem cell23_4089765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_4089765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089765 prefixEnd_4089765 := by exact prefixLift 4089765
  have htrace : WordTrace (prefixWord ++ tailWord_4089765) baseStart_4089765 baseEnd_4089765 := by
    simpa [prefixWord, tailWord_4089765, baseEnd_4089765] using wordTrace_append hprefix tailTrace_4089765
  have hstable : (prefixWord ++ tailWord_4089765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089765).length < 2 ^ (prefixWord ++ tailWord_4089765).sum := by decide
  have hdescent : baseEnd_4089765 < baseStart_4089765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089792 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 2, 4]
def baseStart_4089792 : Nat := 118140960795 + 4089792 * 2 ^ 59
def prefixEnd_4089792 : Nat := 4983230072969 + 3 ^ 40 * 4089792 * 2
def baseEnd_4089792 : Nat := 700009690970989301230465

theorem tailTrace_4089792 : CollatzResearch.WordTrace tailWord_4089792 prefixEnd_4089792 700009690970989301230465 := by
  unfold tailWord_4089792
  simp only [CollatzResearch.WordTrace]
  refine ⟨74583484399694769854903815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99444645866259693139871753 74583484399694769854903815)
  ·
    refine ⟨111875226599542154782355723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74583484399694769854903815 111875226599542154782355723)
    ·
      refine ⟨167812839899313232173533585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111875226599542154782355723 167812839899313232173533585)
      ·
        refine ⟨125859629924484924130150189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167812839899313232173533585 125859629924484924130150189)
        ·
          refine ⟨47197361221681846548806321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125859629924484924130150189 47197361221681846548806321)
          ·
            refine ⟨35398020916261384911604741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47197361221681846548806321 35398020916261384911604741)
            ·
              refine ⟨6637128921799009670925889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35398020916261384911604741 6637128921799009670925889)
              ·
                refine ⟨4977846691349257253194417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6637128921799009670925889 4977846691349257253194417)
                ·
                  refine ⟨3733385018511942939895813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4977846691349257253194417 3733385018511942939895813)
                  ·
                    refine ⟨700009690970989301230465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3733385018511942939895813 700009690970989301230465)
                    ·
                      rfl

theorem cell23_4089792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2, 4].length) (baseStart_4089792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089792 prefixEnd_4089792 := by exact prefixLift 4089792
  have htrace : WordTrace (prefixWord ++ tailWord_4089792) baseStart_4089792 baseEnd_4089792 := by
    simpa [prefixWord, tailWord_4089792, baseEnd_4089792] using wordTrace_append hprefix tailTrace_4089792
  have hstable : (prefixWord ++ tailWord_4089792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089792).length < 2 ^ (prefixWord ++ tailWord_4089792).sum := by decide
  have hdescent : baseEnd_4089792 < baseStart_4089792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089808 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_4089808 : Nat := 118140960795 + 4089808 * 2 ^ 59
def prefixEnd_4089808 : Nat := 4983230072969 + 3 ^ 40 * 4089808 * 2
def baseEnd_4089808 : Nat := 2100037288603439841091321

theorem tailTrace_4089808 : CollatzResearch.WordTrace tailWord_4089808 prefixEnd_4089808 2100037288603439841091321 := by
  unfold tailWord_4089808
  simp only [CollatzResearch.WordTrace]
  refine ⟨74583776183665787221195039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99445034911554382961593385 74583776183665787221195039)
  ·
    refine ⟨111875664275498680831792559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74583776183665787221195039 111875664275498680831792559)
    ·
      refine ⟨167813496413248021247688839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111875664275498680831792559 167813496413248021247688839)
      ·
        refine ⟨251720244619872031871533259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167813496413248021247688839 251720244619872031871533259)
        ·
          refine ⟨377580366929808047807299889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251720244619872031871533259 377580366929808047807299889)
          ·
            refine ⟨283185275197356035855474917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377580366929808047807299889 283185275197356035855474917)
            ·
              refine ⟨53097239099504256722901547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283185275197356035855474917 53097239099504256722901547)
              ·
                refine ⟨79645858649256385084352321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53097239099504256722901547 79645858649256385084352321)
                ·
                  refine ⟨59734393986942288813264241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79645858649256385084352321 59734393986942288813264241)
                  ·
                    refine ⟨44800795490206716609948181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59734393986942288813264241 44800795490206716609948181)
                    ·
                      refine ⟨2100037288603439841091321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44800795490206716609948181 2100037288603439841091321)
                      ·
                        rfl

theorem cell23_4089808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_4089808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089808 prefixEnd_4089808 := by exact prefixLift 4089808
  have htrace : WordTrace (prefixWord ++ tailWord_4089808) baseStart_4089808 baseEnd_4089808 := by
    simpa [prefixWord, tailWord_4089808, baseEnd_4089808] using wordTrace_append hprefix tailTrace_4089808
  have hstable : (prefixWord ++ tailWord_4089808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089808).length < 2 ^ (prefixWord ++ tailWord_4089808).sum := by decide
  have hdescent : baseEnd_4089808 < baseStart_4089808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089812 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_4089812 : Nat := 118140960795 + 4089812 * 2 ^ 59
def prefixEnd_4089812 : Nat := 4983230072969 + 3 ^ 40 * 4089812 * 2
def baseEnd_4089812 : Nat := 2100039342526057825441303

theorem tailTrace_4089812 : CollatzResearch.WordTrace tailWord_4089812 prefixEnd_4089812 2100039342526057825441303 := by
  unfold tailWord_4089812
  simp only [CollatzResearch.WordTrace]
  refine ⟨74583849129658541562767845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99445132172878055417023793 74583849129658541562767845)
  ·
    refine ⟨13984471711810976543018971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74583849129658541562767845 13984471711810976543018971)
    ·
      refine ⟨20976707567716464814528457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13984471711810976543018971 20976707567716464814528457)
      ·
        refine ⟨15732530675787348610896343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20976707567716464814528457 15732530675787348610896343)
        ·
          refine ⟨23598796013681022916344515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15732530675787348610896343 23598796013681022916344515)
          ·
            refine ⟨35398194020521534374516773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23598796013681022916344515 35398194020521534374516773)
            ·
              refine ⟨6637161378847787695221895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35398194020521534374516773 6637161378847787695221895)
              ·
                refine ⟨9955742068271681542832843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6637161378847787695221895 9955742068271681542832843)
                ·
                  refine ⟨14933613102407522314249265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9955742068271681542832843 14933613102407522314249265)
                  ·
                    refine ⟨11200209826805641735686949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14933613102407522314249265 11200209826805641735686949)
                    ·
                      refine ⟨2100039342526057825441303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11200209826805641735686949 2100039342526057825441303)
                      ·
                        rfl

theorem cell23_4089812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_4089812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089812 prefixEnd_4089812 := by exact prefixLift 4089812
  have htrace : WordTrace (prefixWord ++ tailWord_4089812) baseStart_4089812 baseEnd_4089812 := by
    simpa [prefixWord, tailWord_4089812, baseEnd_4089812] using wordTrace_append hprefix tailTrace_4089812
  have hstable : (prefixWord ++ tailWord_4089812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089812).length < 2 ^ (prefixWord ++ tailWord_4089812).sum := by decide
  have hdescent : baseEnd_4089812 < baseStart_4089812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089820 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4089820 : Nat := 118140960795 + 4089820 * 2 ^ 59
def prefixEnd_4089820 : Nat := 4983230072969 + 3 ^ 40 * 4089820 * 2
def baseEnd_4089820 : Nat := 2100043450371293794141267

theorem tailTrace_4089820 : CollatzResearch.WordTrace tailWord_4089820 prefixEnd_4089820 2100043450371293794141267 := by
  unfold tailWord_4089820
  simp only [CollatzResearch.WordTrace]
  refine ⟨74583995021644050245913457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99445326695525400327884609 74583995021644050245913457)
  ·
    refine ⟨55937996266233037684435093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74583995021644050245913457 55937996266233037684435093)
    ·
      refine ⟨2622093574979673641457895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55937996266233037684435093 2622093574979673641457895)
      ·
        refine ⟨3933140362469510462186843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2622093574979673641457895 3933140362469510462186843)
        ·
          refine ⟨5899710543704265693280265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3933140362469510462186843 5899710543704265693280265)
          ·
            refine ⟨4424782907778199269960199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5899710543704265693280265 4424782907778199269960199)
            ·
              refine ⟨6637174361667298904940299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424782907778199269960199 6637174361667298904940299)
              ·
                refine ⟨9955761542500948357410449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6637174361667298904940299 9955761542500948357410449)
                ·
                  refine ⟨7466821156875711268057837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9955761542500948357410449 7466821156875711268057837)
                  ·
                    refine ⟨2800057933828391725521689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7466821156875711268057837 2800057933828391725521689)
                    ·
                      refine ⟨2100043450371293794141267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800057933828391725521689 2100043450371293794141267)
                      ·
                        rfl

theorem cell23_4089820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4089820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089820 prefixEnd_4089820 := by exact prefixLift 4089820
  have htrace : WordTrace (prefixWord ++ tailWord_4089820) baseStart_4089820 baseEnd_4089820 := by
    simpa [prefixWord, tailWord_4089820, baseEnd_4089820] using wordTrace_append hprefix tailTrace_4089820
  have hstable : (prefixWord ++ tailWord_4089820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089820).length < 2 ^ (prefixWord ++ tailWord_4089820).sum := by decide
  have hdescent : baseEnd_4089820 < baseStart_4089820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089832 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_4089832 : Nat := 118140960795 + 4089832 * 2 ^ 59
def prefixEnd_4089832 : Nat := 4983230072969 + 3 ^ 40 * 4089832 * 2
def baseEnd_4089832 : Nat := 2100049612139147747191211

theorem tailTrace_4089832 : CollatzResearch.WordTrace tailWord_4089832 prefixEnd_4089832 2100049612139147747191211 := by
  unfold tailWord_4089832
  simp only [CollatzResearch.WordTrace]
  refine ⟨74584213859622313270631875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99445618479496417694175833 74584213859622313270631875)
  ·
    refine ⟨111876320789433469905947813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74584213859622313270631875 111876320789433469905947813)
    ·
      refine ⟨20976810148018775607365215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111876320789433469905947813 20976810148018775607365215)
      ·
        refine ⟨31465215222028163411047823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20976810148018775607365215 31465215222028163411047823)
        ·
          refine ⟨47197822833042245116571735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31465215222028163411047823 47197822833042245116571735)
          ·
            refine ⟨70796734249563367674857603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47197822833042245116571735 70796734249563367674857603)
            ·
              refine ⟨106195101374345051512286405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70796734249563367674857603 106195101374345051512286405)
              ·
                refine ⟨19911581507689697158553701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106195101374345051512286405 19911581507689697158553701)
                ·
                  refine ⟨3733421532691818217228819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19911581507689697158553701 3733421532691818217228819)
                  ·
                    refine ⟨5600132299037727325843229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3733421532691818217228819 5600132299037727325843229)
                    ·
                      refine ⟨2100049612139147747191211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5600132299037727325843229 2100049612139147747191211)
                      ·
                        rfl

theorem cell23_4089832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_4089832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089832 prefixEnd_4089832 := by exact prefixLift 4089832
  have htrace : WordTrace (prefixWord ++ tailWord_4089832) baseStart_4089832 baseEnd_4089832 := by
    simpa [prefixWord, tailWord_4089832, baseEnd_4089832] using wordTrace_append hprefix tailTrace_4089832
  have hstable : (prefixWord ++ tailWord_4089832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089832).length < 2 ^ (prefixWord ++ tailWord_4089832).sum := by decide
  have hdescent : baseEnd_4089832 < baseStart_4089832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089849 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 2, 1, 3]
def baseStart_4089849 : Nat := 118140960795 + 4089849 * 2 ^ 59
def prefixEnd_4089849 : Nat := 4983230072969 + 3 ^ 40 * 4089849 * 2
def baseEnd_4089849 : Nat := 2100058341310274180678633

theorem tailTrace_4089849 : CollatzResearch.WordTrace tailWord_4089849 prefixEnd_4089849 2100058341310274180678633 := by
  unfold tailWord_4089849
  simp only [CollatzResearch.WordTrace]
  refine ⟨149169047760183038444632601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99446031840122025629755067 149169047760183038444632601)
  ·
    refine ⟨111876785820137278833474451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149169047760183038444632601 111876785820137278833474451)
    ·
      refine ⟨167815178730205918250211677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111876785820137278833474451 167815178730205918250211677)
      ·
        refine ⟨62930692023827219343829379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167815178730205918250211677 62930692023827219343829379)
        ·
          refine ⟨94396038035740829015744069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62930692023827219343829379 94396038035740829015744069)
          ·
            refine ⟨17699257131701405440452013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94396038035740829015744069 17699257131701405440452013)
            ·
              refine ⟨6637221424388027040169505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17699257131701405440452013 6637221424388027040169505)
              ·
                refine ⟨4977916068291020280127129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6637221424388027040169505 4977916068291020280127129)
                ·
                  refine ⟨3733437051218265210095347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4977916068291020280127129 3733437051218265210095347)
                  ·
                    refine ⟨5600155576827397815143021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3733437051218265210095347 5600155576827397815143021)
                    ·
                      refine ⟨2100058341310274180678633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5600155576827397815143021 2100058341310274180678633)
                      ·
                        rfl

theorem cell23_4089849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_4089849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089849 prefixEnd_4089849 := by exact prefixLift 4089849
  have htrace : WordTrace (prefixWord ++ tailWord_4089849) baseStart_4089849 baseEnd_4089849 := by
    simpa [prefixWord, tailWord_4089849, baseEnd_4089849] using wordTrace_append hprefix tailTrace_4089849
  have hstable : (prefixWord ++ tailWord_4089849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089849).length < 2 ^ (prefixWord ++ tailWord_4089849).sum := by decide
  have hdescent : baseEnd_4089849 < baseStart_4089849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089866 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3]
def baseStart_4089866 : Nat := 118140960795 + 4089866 * 2 ^ 59
def prefixEnd_4089866 : Nat := 4983230072969 + 3 ^ 40 * 4089866 * 2
def baseEnd_4089866 : Nat := 2100067070481400614166055

theorem tailTrace_4089866 : CollatzResearch.WordTrace tailWord_4089866 prefixEnd_4089866 2100067070481400614166055 := by
  unfold tailWord_4089866
  simp only [CollatzResearch.WordTrace]
  refine ⟨37292416950280362587000363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99446445200747633565334301 37292416950280362587000363)
  ·
    refine ⟨55938625425420543880500545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37292416950280362587000363 55938625425420543880500545)
    ·
      refine ⟨41953969069065407910375409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55938625425420543880500545 41953969069065407910375409)
      ·
        refine ⟨31465476801799055932781557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41953969069065407910375409 31465476801799055932781557)
        ·
          refine ⟨2949888450168661493698271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31465476801799055932781557 2949888450168661493698271)
          ·
            refine ⟨4424832675252992240547407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949888450168661493698271 4424832675252992240547407)
            ·
              refine ⟨6637249012879488360821111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424832675252992240547407 6637249012879488360821111)
              ·
                refine ⟨9955873519319232541231667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6637249012879488360821111 9955873519319232541231667)
                ·
                  refine ⟨14933810278978848811847501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9955873519319232541231667 14933810278978848811847501)
                  ·
                    refine ⟨5600178854617068304442813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14933810278978848811847501 5600178854617068304442813)
                    ·
                      refine ⟨2100067070481400614166055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5600178854617068304442813 2100067070481400614166055)
                      ·
                        rfl

theorem cell23_4089866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_4089866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089866 prefixEnd_4089866 := by exact prefixLift 4089866
  have htrace : WordTrace (prefixWord ++ tailWord_4089866) baseStart_4089866 baseEnd_4089866 := by
    simpa [prefixWord, tailWord_4089866, baseEnd_4089866] using wordTrace_append hprefix tailTrace_4089866
  have hstable : (prefixWord ++ tailWord_4089866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089866).length < 2 ^ (prefixWord ++ tailWord_4089866).sum := by decide
  have hdescent : baseEnd_4089866 < baseStart_4089866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089875 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 3]
def baseStart_4089875 : Nat := 118140960795 + 4089875 * 2 ^ 59
def prefixEnd_4089875 : Nat := 4983230072969 + 3 ^ 40 * 4089875 * 2
def baseEnd_4089875 : Nat := 2100071691807291078953513

theorem tailTrace_4089875 : CollatzResearch.WordTrace tailWord_4089875 prefixEnd_4089875 2100071691807291078953513 := by
  unfold tailWord_4089875
  simp only [CollatzResearch.WordTrace]
  refine ⟨149169996058088844885079079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99446664038725896590052719 149169996058088844885079079)
  ·
    refine ⟨223754994087133267327618619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149169996058088844885079079 223754994087133267327618619)
    ·
      refine ⟨335632491130699900991427929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223754994087133267327618619 335632491130699900991427929)
      ·
        refine ⟨251724368348024925743570947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335632491130699900991427929 251724368348024925743570947)
        ·
          refine ⟨377586552522037388615356421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251724368348024925743570947 377586552522037388615356421)
          ·
            refine ⟨70797478597882010365379329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377586552522037388615356421 70797478597882010365379329)
            ·
              refine ⟨53098108948411507774034497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70797478597882010365379329 53098108948411507774034497)
              ·
                refine ⟨39823581711308630830525873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53098108948411507774034497 39823581711308630830525873)
                ·
                  refine ⟨29867686283481473122894405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39823581711308630830525873 29867686283481473122894405)
                  ·
                    refine ⟨5600191178152776210542701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29867686283481473122894405 5600191178152776210542701)
                    ·
                      refine ⟨2100071691807291078953513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5600191178152776210542701 2100071691807291078953513)
                      ·
                        rfl

theorem cell23_4089875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 3].length) (baseStart_4089875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089875 prefixEnd_4089875 := by exact prefixLift 4089875
  have htrace : WordTrace (prefixWord ++ tailWord_4089875) baseStart_4089875 baseEnd_4089875 := by
    simpa [prefixWord, tailWord_4089875, baseEnd_4089875] using wordTrace_append hprefix tailTrace_4089875
  have hstable : (prefixWord ++ tailWord_4089875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089875).length < 2 ^ (prefixWord ++ tailWord_4089875).sum := by decide
  have hdescent : baseEnd_4089875 < baseStart_4089875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089925 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_4089925 : Nat := 118140960795 + 4089925 * 2 ^ 59
def prefixEnd_4089925 : Nat := 4983230072969 + 3 ^ 40 * 4089925 * 2
def baseEnd_4089925 : Nat := 700032455280005294442761

theorem tailTrace_4089925 : CollatzResearch.WordTrace tailWord_4089925 prefixEnd_4089925 700032455280005294442761 := by
  unfold tailWord_4089925
  simp only [CollatzResearch.WordTrace]
  refine ⟨149171819707907703424399229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99447879805271802282932819 149171819707907703424399229)
  ·
    refine ⟨55939432390465388784149711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149171819707907703424399229 55939432390465388784149711)
    ·
      refine ⟨83909148585698083176224567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55939432390465388784149711 83909148585698083176224567)
      ·
        refine ⟨125863722878547124764336851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83909148585698083176224567 125863722878547124764336851)
        ·
          refine ⟨188795584317820687146505277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125863722878547124764336851 188795584317820687146505277)
          ·
            refine ⟨70798344119182757679939479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188795584317820687146505277 70798344119182757679939479)
            ·
              refine ⟨106197516178774136519909219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70798344119182757679939479 106197516178774136519909219)
              ·
                refine ⟨159296274268161204779863829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106197516178774136519909219 159296274268161204779863829)
                ·
                  refine ⟨7467012856320056474056117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159296274268161204779863829 7467012856320056474056117)
                  ·
                    refine ⟨700032455280005294442761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7467012856320056474056117 700032455280005294442761)
                    ·
                      rfl

theorem cell23_4089925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_4089925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089925 prefixEnd_4089925 := by exact prefixLift 4089925
  have htrace : WordTrace (prefixWord ++ tailWord_4089925) baseStart_4089925 baseEnd_4089925 := by
    simpa [prefixWord, tailWord_4089925, baseEnd_4089925] using wordTrace_append hprefix tailTrace_4089925
  have hstable : (prefixWord ++ tailWord_4089925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089925).length < 2 ^ (prefixWord ++ tailWord_4089925).sum := by decide
  have hdescent : baseEnd_4089925 < baseStart_4089925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4089989 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 3, 4]
def baseStart_4089989 : Nat := 118140960795 + 4089989 * 2 ^ 59
def prefixEnd_4089989 : Nat := 4983230072969 + 3 ^ 40 * 4089989 * 2
def baseEnd_4089989 : Nat := 700043409533967877642663

theorem tailTrace_4089989 : CollatzResearch.WordTrace tailWord_4089989 prefixEnd_4089989 700043409533967877642663 := by
  unfold tailWord_4089989
  simp only [CollatzResearch.WordTrace]
  refine ⟨149174153979675842354729021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99449435986450561569819347 149174153979675842354729021)
  ·
    refine ⟨55940307742378440883023383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149174153979675842354729021 55940307742378440883023383)
    ·
      refine ⟨83910461613567661324535075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55940307742378440883023383 83910461613567661324535075)
      ·
        refine ⟨125865692420351491986802613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83910461613567661324535075 125865692420351491986802613)
        ·
          refine ⟨11799908664407952373762745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125865692420351491986802613 11799908664407952373762745)
          ·
            refine ⟨8849931498305964280322059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11799908664407952373762745 8849931498305964280322059)
            ·
              refine ⟨13274897247458946420483089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8849931498305964280322059 13274897247458946420483089)
              ·
                refine ⟨9956172935594209815362317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13274897247458946420483089 9956172935594209815362317)
                ·
                  refine ⟨3733564850847828680760869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9956172935594209815362317 3733564850847828680760869)
                  ·
                    refine ⟨700043409533967877642663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3733564850847828680760869 700043409533967877642663)
                    ·
                      rfl

theorem cell23_4089989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_4089989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4089989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4089989 prefixEnd_4089989 := by exact prefixLift 4089989
  have htrace : WordTrace (prefixWord ++ tailWord_4089989) baseStart_4089989 baseEnd_4089989 := by
    simpa [prefixWord, tailWord_4089989, baseEnd_4089989] using wordTrace_append hprefix tailTrace_4089989
  have hstable : (prefixWord ++ tailWord_4089989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4089989).length < 2 ^ (prefixWord ++ tailWord_4089989).sum := by decide
  have hdescent : baseEnd_4089989 < baseStart_4089989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4089989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090002 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 8]
def baseStart_4090002 : Nat := 118140960795 + 4090002 * 2 ^ 59
def prefixEnd_4090002 : Nat := 4983230072969 + 3 ^ 40 * 4090002 * 2
def baseEnd_4090002 : Nat := 233348544872268009118381

theorem tailTrace_4090002 : CollatzResearch.WordTrace tailWord_4090002 prefixEnd_4090002 233348544872268009118381 := by
  unfold tailWord_4090002
  simp only [CollatzResearch.WordTrace]
  refine ⟨37293657032157186393738065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99449752085752497049968173 37293657032157186393738065)
  ·
    refine ⟨27970242774117889795303549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37293657032157186393738065 27970242774117889795303549)
    ·
      refine ⟨10488841040294208673238831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27970242774117889795303549 10488841040294208673238831)
      ·
        refine ⟨15733261560441313009858247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10488841040294208673238831 15733261560441313009858247)
        ·
          refine ⟨23599892340661969514787371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15733261560441313009858247 23599892340661969514787371)
          ·
            refine ⟨35399838510992954272181057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23599892340661969514787371 35399838510992954272181057)
            ·
              refine ⟨26549878883244715704135793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35399838510992954272181057 26549878883244715704135793)
              ·
                refine ⟨19912409162433536778101845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26549878883244715704135793 19912409162433536778101845)
                ·
                  refine ⟨233348544872268009118381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19912409162433536778101845 233348544872268009118381)
                  ·
                    rfl

theorem cell23_4090002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_4090002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090002 prefixEnd_4090002 := by exact prefixLift 4090002
  have htrace : WordTrace (prefixWord ++ tailWord_4090002) baseStart_4090002 baseEnd_4090002 := by
    simpa [prefixWord, tailWord_4090002, baseEnd_4090002] using wordTrace_append hprefix tailTrace_4090002
  have hstable : (prefixWord ++ tailWord_4090002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090002).length < 2 ^ (prefixWord ++ tailWord_4090002).sum := by decide
  have hdescent : baseEnd_4090002 < baseStart_4090002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090039 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 1, 5, 2]
def baseStart_4090039 : Nat := 118140960795 + 4090039 * 2 ^ 59
def prefixEnd_4090039 : Nat := 4983230072969 + 3 ^ 40 * 4090039 * 2
def baseEnd_4090039 : Nat := 2100155902634628437302759

theorem tailTrace_4090039 : CollatzResearch.WordTrace tailWord_4090039 prefixEnd_4090039 2100155902634628437302759 := by
  unfold tailWord_4090039
  simp only [CollatzResearch.WordTrace]
  refine ⟨149175977629494700894049171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99450651752996467262699447 149175977629494700894049171)
  ·
    refine ⟨223763966444242051341073757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149175977629494700894049171 223763966444242051341073757)
    ·
      refine ⟨83911487416590769252902659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223763966444242051341073757 83911487416590769252902659)
      ·
        refine ⟨125867231124886153879353989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83911487416590769252902659 125867231124886153879353989)
        ·
          refine ⟨23600105835916153852378873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125867231124886153879353989 23600105835916153852378873)
          ·
            refine ⟨17700079376937115389284155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23600105835916153852378873 17700079376937115389284155)
            ·
              refine ⟨26550119065405673083926233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17700079376937115389284155 26550119065405673083926233)
              ·
                refine ⟨19912589299054254812944675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26550119065405673083926233 19912589299054254812944675)
                ·
                  refine ⟨29868883948581382219417013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19912589299054254812944675 29868883948581382219417013)
                  ·
                    refine ⟨2800207870179504583070345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29868883948581382219417013 2800207870179504583070345)
                    ·
                      refine ⟨2100155902634628437302759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800207870179504583070345 2100155902634628437302759)
                      ·
                        rfl

theorem cell23_4090039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 5, 2].length) (baseStart_4090039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090039 prefixEnd_4090039 := by exact prefixLift 4090039
  have htrace : WordTrace (prefixWord ++ tailWord_4090039) baseStart_4090039 baseEnd_4090039 := by
    simpa [prefixWord, tailWord_4090039, baseEnd_4090039] using wordTrace_append hprefix tailTrace_4090039
  have hstable : (prefixWord ++ tailWord_4090039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090039).length < 2 ^ (prefixWord ++ tailWord_4090039).sum := by decide
  have hdescent : baseEnd_4090039 < baseStart_4090039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090079 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 2, 4]
def baseStart_4090079 : Nat := 118140960795 + 4090079 * 2 ^ 59
def prefixEnd_4090079 : Nat := 4983230072969 + 3 ^ 40 * 4090079 * 2
def baseEnd_4090079 : Nat := 700058813953602760267525

theorem tailTrace_4090079 : CollatzResearch.WordTrace tailWord_4090079 prefixEnd_4090079 700058813953602760267525 := by
  unfold tailWord_4090079
  simp only [CollatzResearch.WordTrace]
  refine ⟨149177436549349787725505291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99451624366233191817003527 149177436549349787725505291)
  ·
    refine ⟨223766154824024681588257937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149177436549349787725505291 223766154824024681588257937)
    ·
      refine ⟨167824616118018511191193453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223766154824024681588257937 167824616118018511191193453)
      ·
        refine ⟨62934231044256941696697545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167824616118018511191193453 62934231044256941696697545)
        ·
          refine ⟨47200673283192706272523159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62934231044256941696697545 47200673283192706272523159)
          ·
            refine ⟨70801009924789059408784739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47200673283192706272523159 70801009924789059408784739)
            ·
              refine ⟨106201514887183589113177109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70801009924789059408784739 106201514887183589113177109)
              ·
                refine ⟨4978196010336730739680177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106201514887183589113177109 4978196010336730739680177)
                ·
                  refine ⟨3733647007752548054760133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4978196010336730739680177 3733647007752548054760133)
                  ·
                    refine ⟨700058813953602760267525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3733647007752548054760133 700058813953602760267525)
                    ·
                      rfl

theorem cell23_4090079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 4].length) (baseStart_4090079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090079 prefixEnd_4090079 := by exact prefixLift 4090079
  have htrace : WordTrace (prefixWord ++ tailWord_4090079) baseStart_4090079 baseEnd_4090079 := by
    simpa [prefixWord, tailWord_4090079, baseEnd_4090079] using wordTrace_append hprefix tailTrace_4090079
  have hstable : (prefixWord ++ tailWord_4090079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090079).length < 2 ^ (prefixWord ++ tailWord_4090079).sum := by decide
  have hdescent : baseEnd_4090079 < baseStart_4090079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090092 : List Nat := [2, 2, 1, 1, 2, 3, 4, 8]
def baseStart_4090092 : Nat := 118140960795 + 4090092 * 2 ^ 59
def prefixEnd_4090092 : Nat := 4983230072969 + 3 ^ 40 * 4090092 * 2
def baseEnd_4090092 : Nat := 77784559892937656664445

theorem tailTrace_4090092 : CollatzResearch.WordTrace tailWord_4090092 prefixEnd_4090092 77784559892937656664445 := by
  unfold tailWord_4090092
  simp only [CollatzResearch.WordTrace]
  refine ⟨74588955349151345472864265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99451940465535127297152353 74588955349151345472864265)
  ·
    refine ⟨55941716511863509104648199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74588955349151345472864265 55941716511863509104648199)
    ·
      refine ⟨83912574767795263656972299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55941716511863509104648199 83912574767795263656972299)
      ·
        refine ⟨125868862151692895485458449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83912574767795263656972299 125868862151692895485458449)
        ·
          refine ⟨94401646613769671614093837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125868862151692895485458449 94401646613769671614093837)
          ·
            refine ⟨35400617480163626855285189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94401646613769671614093837 35400617480163626855285189)
            ·
              refine ⟨6637615777530680035365973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35400617480163626855285189 6637615777530680035365973)
              ·
                refine ⟨77784559892937656664445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6637615777530680035365973 77784559892937656664445)
                ·
                  rfl

theorem cell23_4090092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 8].length) (baseStart_4090092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090092 prefixEnd_4090092 := by exact prefixLift 4090092
  have htrace : WordTrace (prefixWord ++ tailWord_4090092) baseStart_4090092 baseEnd_4090092 := by
    simpa [prefixWord, tailWord_4090092, baseEnd_4090092] using wordTrace_append hprefix tailTrace_4090092
  have hstable : (prefixWord ++ tailWord_4090092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090092).length < 2 ^ (prefixWord ++ tailWord_4090092).sum := by decide
  have hdescent : baseEnd_4090092 < baseStart_4090092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090106 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3]
def baseStart_4090106 : Nat := 118140960795 + 4090106 * 2 ^ 59
def prefixEnd_4090106 : Nat := 4983230072969 + 3 ^ 40 * 4090106 * 2
def baseEnd_4090106 : Nat := 2100190305838479675164951

theorem tailTrace_4090106 : CollatzResearch.WordTrace tailWord_4090106 prefixEnd_4090106 2100190305838479675164951 := by
  unfold tailWord_4090106
  simp only [CollatzResearch.WordTrace]
  refine ⟨37294605330062992834184543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99452280880167980891158781 37294605330062992834184543)
  ·
    refine ⟨55941907995094489251276815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37294605330062992834184543 55941907995094489251276815)
    ·
      refine ⟨83912861992641733876915223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55941907995094489251276815 83912861992641733876915223)
      ·
        refine ⟨125869292988962600815372835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83912861992641733876915223 125869292988962600815372835)
        ·
          refine ⟨188803939483443901223059253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125869292988962600815372835 188803939483443901223059253)
          ·
            refine ⟨17700369326572865739661805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188803939483443901223059253 17700369326572865739661805)
            ·
              refine ⟨6637638497464824652373177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17700369326572865739661805 6637638497464824652373177)
              ·
                refine ⟨4978228873098618489279883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6637638497464824652373177 4978228873098618489279883)
                ·
                  refine ⟨7467343309647927733919825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4978228873098618489279883 7467343309647927733919825)
                  ·
                    refine ⟨5600507482235945800439869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7467343309647927733919825 5600507482235945800439869)
                    ·
                      refine ⟨2100190305838479675164951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5600507482235945800439869 2100190305838479675164951)
                      ·
                        rfl

theorem cell23_4090106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_4090106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090106 prefixEnd_4090106 := by exact prefixLift 4090106
  have htrace : WordTrace (prefixWord ++ tailWord_4090106) baseStart_4090106 baseEnd_4090106 := by
    simpa [prefixWord, tailWord_4090106, baseEnd_4090106] using wordTrace_append hprefix tailTrace_4090106
  have hstable : (prefixWord ++ tailWord_4090106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090106).length < 2 ^ (prefixWord ++ tailWord_4090106).sum := by decide
  have hdescent : baseEnd_4090106 < baseStart_4090106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090116 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_4090116 : Nat := 118140960795 + 4090116 * 2 ^ 59
def prefixEnd_4090116 : Nat := 4983230072969 + 3 ^ 40 * 4090116 * 2
def baseEnd_4090116 : Nat := 2100195440645024636039905

theorem tailTrace_4090116 : CollatzResearch.WordTrace tailWord_4090116 prefixEnd_4090116 2100195440645024636039905 := by
  unfold tailWord_4090116
  simp only [CollatzResearch.WordTrace]
  refine ⟨74589393025107871522301101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99452524033477162029734801 74589393025107871522301101)
  ·
    refine ⟨27971022384415451820862913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74589393025107871522301101 27971022384415451820862913)
    ·
      refine ⟨20978266788311588865647185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27971022384415451820862913 20978266788311588865647185)
      ·
        refine ⟨15733700091233691649235389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20978266788311588865647185 15733700091233691649235389)
        ·
          refine ⟨5900137534212634368463271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15733700091233691649235389 5900137534212634368463271)
          ·
            refine ⟨8850206301318951552694907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5900137534212634368463271 8850206301318951552694907)
            ·
              refine ⟨13275309451978427329042361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8850206301318951552694907 13275309451978427329042361)
              ·
                refine ⟨9956482088983820496781771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13275309451978427329042361 9956482088983820496781771)
                ·
                  refine ⟨14934723133475730745172657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9956482088983820496781771 14934723133475730745172657)
                  ·
                    refine ⟨11201042350106798058879493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14934723133475730745172657 11201042350106798058879493)
                    ·
                      refine ⟨2100195440645024636039905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11201042350106798058879493 2100195440645024636039905)
                      ·
                        rfl

theorem cell23_4090116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_4090116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090116 prefixEnd_4090116 := by exact prefixLift 4090116
  have htrace : WordTrace (prefixWord ++ tailWord_4090116) baseStart_4090116 baseEnd_4090116 := by
    simpa [prefixWord, tailWord_4090116, baseEnd_4090116] using wordTrace_append hprefix tailTrace_4090116
  have hstable : (prefixWord ++ tailWord_4090116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090116).length < 2 ^ (prefixWord ++ tailWord_4090116).sum := by decide
  have hdescent : baseEnd_4090116 < baseStart_4090116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090193 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 4, 2, 2]
def baseStart_4090193 : Nat := 118140960795 + 4090193 * 2 ^ 59
def prefixEnd_4090193 : Nat := 4983230072969 + 3 ^ 40 * 4090193 * 2
def baseEnd_4090193 : Nat := 2100234978655420834777051

theorem tailTrace_4090193 : CollatzResearch.WordTrace tailWord_4090193 prefixEnd_4090193 2100234978655420834777051 := by
  unfold tailWord_4090193
  simp only [CollatzResearch.WordTrace]
  refine ⟨149181594470936785195155233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99454396313957856796770155 149181594470936785195155233)
  ·
    refine ⟨111886195853202588896366425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149181594470936785195155233 111886195853202588896366425)
    ·
      refine ⟨83914646889901941672274819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111886195853202588896366425 83914646889901941672274819)
      ·
        refine ⟨125871970334852912508412229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83914646889901941672274819 125871970334852912508412229)
        ·
          refine ⟨23600994437784921095327293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125871970334852912508412229 23600994437784921095327293)
          ·
            refine ⟨8850372914169345410747735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23600994437784921095327293 8850372914169345410747735)
            ·
              refine ⟨13275559371254018116121603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8850372914169345410747735 13275559371254018116121603)
              ·
                refine ⟨19913339056881027174182405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13275559371254018116121603 19913339056881027174182405)
                ·
                  refine ⟨3733751073165192595159201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19913339056881027174182405 3733751073165192595159201)
                  ·
                    refine ⟨2800313304873894446369401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3733751073165192595159201 2800313304873894446369401)
                    ·
                      refine ⟨2100234978655420834777051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800313304873894446369401 2100234978655420834777051)
                      ·
                        rfl

theorem cell23_4090193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 2, 2].length) (baseStart_4090193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090193 prefixEnd_4090193 := by exact prefixLift 4090193
  have htrace : WordTrace (prefixWord ++ tailWord_4090193) baseStart_4090193 baseEnd_4090193 := by
    simpa [prefixWord, tailWord_4090193, baseEnd_4090193] using wordTrace_append hprefix tailTrace_4090193
  have hstable : (prefixWord ++ tailWord_4090193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090193).length < 2 ^ (prefixWord ++ tailWord_4090193).sum := by decide
  have hdescent : baseEnd_4090193 < baseStart_4090193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090199 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 7]
def baseStart_4090199 : Nat := 118140960795 + 4090199 * 2 ^ 59
def prefixEnd_4090199 : Nat := 4983230072969 + 3 ^ 40 * 4090199 * 2
def baseEnd_4090199 : Nat := 233359784393260867922447

theorem tailTrace_4090199 : CollatzResearch.WordTrace tailWord_4090199 prefixEnd_4090199 233359784393260867922447 := by
  unfold tailWord_4090199
  simp only [CollatzResearch.WordTrace]
  refine ⟨149181813308915048219873651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99454542205943365479915767 149181813308915048219873651)
  ·
    refine ⟨223772719963372572329810477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149181813308915048219873651 223772719963372572329810477)
    ·
      refine ⟨83914769986264714623678929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223772719963372572329810477 83914769986264714623678929)
      ·
        refine ⟨62936077489698535967759197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83914769986264714623678929 62936077489698535967759197)
        ·
          refine ⟨23601029058636950987909699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62936077489698535967759197 23601029058636950987909699)
          ·
            refine ⟨35401543587955426481864549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23601029058636950987909699 35401543587955426481864549)
            ·
              refine ⟨6637789422741642465349603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35401543587955426481864549 6637789422741642465349603)
              ·
                refine ⟨9956684134112463698024405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6637789422741642465349603 9956684134112463698024405)
                ·
                  refine ⟨233359784393260867922447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9956684134112463698024405 233359784393260867922447)
                  ·
                    rfl

theorem cell23_4090199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 7].length) (baseStart_4090199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090199 prefixEnd_4090199 := by exact prefixLift 4090199
  have htrace : WordTrace (prefixWord ++ tailWord_4090199) baseStart_4090199 baseEnd_4090199 := by
    simpa [prefixWord, tailWord_4090199, baseEnd_4090199] using wordTrace_append hprefix tailTrace_4090199
  have hstable : (prefixWord ++ tailWord_4090199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090199).length < 2 ^ (prefixWord ++ tailWord_4090199).sum := by decide
  have hdescent : baseEnd_4090199 < baseStart_4090199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090210 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_4090210 : Nat := 118140960795 + 4090210 * 2 ^ 59
def prefixEnd_4090210 : Nat := 4983230072969 + 3 ^ 40 * 4090210 * 2
def baseEnd_4090210 : Nat := 2100243707826547268264473

theorem tailTrace_4090210 : CollatzResearch.WordTrace tailWord_4090210 prefixEnd_4090210 2100243707826547268264473 := by
  unfold tailWord_4090210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37295553627968799274631021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99454809674583464732349389 37295553627968799274631021)
  ·
    refine ⟨13985832610488299727986633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37295553627968799274631021 13985832610488299727986633)
    ·
      refine ⟨10489374457866224795989975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13985832610488299727986633 10489374457866224795989975)
      ·
        refine ⟨15734061686799337193984963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10489374457866224795989975 15734061686799337193984963)
        ·
          refine ⟨23601092530199005790977445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15734061686799337193984963 23601092530199005790977445)
          ·
            refine ⟨4425204849412313585808271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23601092530199005790977445 4425204849412313585808271)
            ·
              refine ⟨6637807274118470378712407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4425204849412313585808271 6637807274118470378712407)
              ·
                refine ⟨9956710911177705568068611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6637807274118470378712407 9956710911177705568068611)
                ·
                  refine ⟨14935066366766558352102917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9956710911177705568068611 14935066366766558352102917)
                  ·
                    refine ⟨2800324943768729691019297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14935066366766558352102917 2800324943768729691019297)
                    ·
                      refine ⟨2100243707826547268264473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800324943768729691019297 2100243707826547268264473)
                      ·
                        rfl

theorem cell23_4090210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_4090210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090210 prefixEnd_4090210 := by exact prefixLift 4090210
  have htrace : WordTrace (prefixWord ++ tailWord_4090210) baseStart_4090210 baseEnd_4090210 := by
    simpa [prefixWord, tailWord_4090210, baseEnd_4090210] using wordTrace_append hprefix tailTrace_4090210
  have hstable : (prefixWord ++ tailWord_4090210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090210).length < 2 ^ (prefixWord ++ tailWord_4090210).sum := by decide
  have hdescent : baseEnd_4090210 < baseStart_4090210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090250 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 7]
def baseStart_4090250 : Nat := 118140960795 + 4090250 * 2 ^ 59
def prefixEnd_4090250 : Nat := 4983230072969 + 3 ^ 40 * 4090250 * 2
def baseEnd_4090250 : Nat := 233362694116969679084921

theorem tailTrace_4090250 : CollatzResearch.WordTrace tailWord_4090250 prefixEnd_4090250 233362694116969679084921 := by
  unfold tailWord_4090250
  simp only [CollatzResearch.WordTrace]
  refine ⟨37295918357932570982495051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99455782287820189286653469 37295918357932570982495051)
  ·
    refine ⟨55943877536898856473742577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37295918357932570982495051 55943877536898856473742577)
    ·
      refine ⟨41957908152674142355306933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55943877536898856473742577 41957908152674142355306933)
      ·
        refine ⟨3933553889313200845810025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41957908152674142355306933 3933553889313200845810025)
        ·
          refine ⟨2950165416984900634357519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3933553889313200845810025 2950165416984900634357519)
          ·
            refine ⟨4425248125477350951536279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950165416984900634357519 4425248125477350951536279)
            ·
              refine ⟨6637872188216026427304419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4425248125477350951536279 6637872188216026427304419)
              ·
                refine ⟨9956808282324039640956629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6637872188216026427304419 9956808282324039640956629)
                ·
                  refine ⟨233362694116969679084921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9956808282324039640956629 233362694116969679084921)
                  ·
                    rfl

theorem cell23_4090250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_4090250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090250 prefixEnd_4090250 := by exact prefixLift 4090250
  have htrace : WordTrace (prefixWord ++ tailWord_4090250) baseStart_4090250 baseEnd_4090250 := by
    simpa [prefixWord, tailWord_4090250, baseEnd_4090250] using wordTrace_append hprefix tailTrace_4090250
  have hstable : (prefixWord ++ tailWord_4090250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090250).length < 2 ^ (prefixWord ++ tailWord_4090250).sum := by decide
  have hdescent : baseEnd_4090250 < baseStart_4090250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090276 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_4090276 : Nat := 118140960795 + 4090276 * 2 ^ 59
def prefixEnd_4090276 : Nat := 4983230072969 + 3 ^ 40 * 4090276 * 2
def baseEnd_4090276 : Nat := 700092532516581336679723

theorem tailTrace_4090276 : CollatzResearch.WordTrace tailWord_4090276 prefixEnd_4090276 700092532516581336679723 := by
  unfold tailWord_4090276
  simp only [CollatzResearch.WordTrace]
  refine ⟨74592310864818045185213341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99456414486424060246951121 74592310864818045185213341)
  ·
    refine ⟨27972116574306766944455003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74592310864818045185213341 27972116574306766944455003)
    ·
      refine ⟨41958174861460150416682505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27972116574306766944455003 41958174861460150416682505)
      ·
        refine ⟨31468631146095112812511879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41958174861460150416682505 31468631146095112812511879)
        ·
          refine ⟨47202946719142669218767819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31468631146095112812511879 47202946719142669218767819)
          ·
            refine ⟨70804420078714003828151729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47202946719142669218767819 70804420078714003828151729)
            ·
              refine ⟨53103315059035502871113797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70804420078714003828151729 53103315059035502871113797)
              ·
                refine ⟨9956871573569156788333837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53103315059035502871113797 9956871573569156788333837)
                ·
                  refine ⟨3733826840088433795625189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9956871573569156788333837 3733826840088433795625189)
                  ·
                    refine ⟨700092532516581336679723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3733826840088433795625189 700092532516581336679723)
                    ·
                      rfl

theorem cell23_4090276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_4090276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090276 prefixEnd_4090276 := by exact prefixLift 4090276
  have htrace : WordTrace (prefixWord ++ tailWord_4090276) baseStart_4090276 baseEnd_4090276 := by
    simpa [prefixWord, tailWord_4090276, baseEnd_4090276] using wordTrace_append hprefix tailTrace_4090276
  have hstable : (prefixWord ++ tailWord_4090276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090276).length < 2 ^ (prefixWord ++ tailWord_4090276).sum := by decide
  have hdescent : baseEnd_4090276 < baseStart_4090276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090299 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 3]
def baseStart_4090299 : Nat := 118140960795 + 4090299 * 2 ^ 59
def prefixEnd_4090299 : Nat := 4983230072969 + 3 ^ 40 * 4090299 * 2
def baseEnd_4090299 : Nat := 2100289407604797420051563

theorem tailTrace_4090299 : CollatzResearch.WordTrace tailWord_4090299 prefixEnd_4090299 2100289407604797420051563 := by
  unfold tailWord_4090299
  simp only [CollatzResearch.WordTrace]
  refine ⟨149185460608552765298513951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99456973739035176865675967 149185460608552765298513951)
  ·
    refine ⟨223778190912829147947770927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149185460608552765298513951 223778190912829147947770927)
    ·
      refine ⟨335667286369243721921656391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223778190912829147947770927 335667286369243721921656391)
      ·
        refine ⟨503500929553865582882484587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335667286369243721921656391 503500929553865582882484587)
        ·
          refine ⟨755251394330798374323726881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503500929553865582882484587 755251394330798374323726881)
          ·
            refine ⟨566438545748098780742795161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755251394330798374323726881 566438545748098780742795161)
            ·
              refine ⟨424828909311074085557096371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566438545748098780742795161 424828909311074085557096371)
              ·
                refine ⟨637243363966611128335644557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424828909311074085557096371 637243363966611128335644557)
                ·
                  refine ⟨238966261487479173125866709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637243363966611128335644557 238966261487479173125866709)
                  ·
                    refine ⟨5600771753612793120137501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 238966261487479173125866709 5600771753612793120137501)
                    ·
                      refine ⟨2100289407604797420051563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5600771753612793120137501 2100289407604797420051563)
                      ·
                        rfl

theorem cell23_4090299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 3].length) (baseStart_4090299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090299 prefixEnd_4090299 := by exact prefixLift 4090299
  have htrace : WordTrace (prefixWord ++ tailWord_4090299) baseStart_4090299 baseEnd_4090299 := by
    simpa [prefixWord, tailWord_4090299, baseEnd_4090299] using wordTrace_append hprefix tailTrace_4090299
  have hstable : (prefixWord ++ tailWord_4090299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090299).length < 2 ^ (prefixWord ++ tailWord_4090299).sum := by decide
  have hdescent : baseEnd_4090299 < baseStart_4090299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090329 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_4090329 : Nat := 118140960795 + 4090329 * 2 ^ 59
def prefixEnd_4090329 : Nat := 4983230072969 + 3 ^ 40 * 4090329 * 2
def baseEnd_4090329 : Nat := 2100304812024432302676425

theorem tailTrace_4090329 : CollatzResearch.WordTrace tailWord_4090329 prefixEnd_4090329 2100304812024432302676425 := by
  unfold tailWord_4090329
  simp only [CollatzResearch.WordTrace]
  refine ⟨149186554798444080422106041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99457703198962720281404027 149186554798444080422106041)
  ·
    refine ⟨111889916098833060316579531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149186554798444080422106041 111889916098833060316579531)
    ·
      refine ⟨167834874148249590474869297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111889916098833060316579531 167834874148249590474869297)
      ·
        refine ⟨125876155611187192856151973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167834874148249590474869297 125876155611187192856151973)
        ·
          refine ⟨23601779177097598660528495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125876155611187192856151973 23601779177097598660528495)
          ·
            refine ⟨35402668765646397990792743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23601779177097598660528495 35402668765646397990792743)
            ·
              refine ⟨53104003148469596986189115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35402668765646397990792743 53104003148469596986189115)
              ·
                refine ⟨79656004722704395479283673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53104003148469596986189115 79656004722704395479283673)
                ·
                  refine ⟨59742003542028296609462755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79656004722704395479283673 59742003542028296609462755)
                  ·
                    refine ⟨89613005313042444914194133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59742003542028296609462755 89613005313042444914194133)
                    ·
                      refine ⟨2100304812024432302676425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89613005313042444914194133 2100304812024432302676425)
                      ·
                        rfl

theorem cell23_4090329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_4090329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090329 prefixEnd_4090329 := by exact prefixLift 4090329
  have htrace : WordTrace (prefixWord ++ tailWord_4090329) baseStart_4090329 baseEnd_4090329 := by
    simpa [prefixWord, tailWord_4090329, baseEnd_4090329] using wordTrace_append hprefix tailTrace_4090329
  have hstable : (prefixWord ++ tailWord_4090329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090329).length < 2 ^ (prefixWord ++ tailWord_4090329).sum := by decide
  have hdescent : baseEnd_4090329 < baseStart_4090329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090336 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 1, 5]
def baseStart_4090336 : Nat := 118140960795 + 4090336 * 2 ^ 59
def prefixEnd_4090336 : Nat := 4983230072969 + 3 ^ 40 * 4090336 * 2
def baseEnd_4090336 : Nat := 700102802129671258429631

theorem tailTrace_4090336 : CollatzResearch.WordTrace tailWord_4090336 prefixEnd_4090336 700102802129671258429631 := by
  unfold tailWord_4090336
  simp only [CollatzResearch.WordTrace]
  refine ⟨74593405054709360308805431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99457873406279147078407241 74593405054709360308805431)
  ·
    refine ⟨111890107582064040463208147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74593405054709360308805431 111890107582064040463208147)
    ·
      refine ⟨167835161373096060694812221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111890107582064040463208147 167835161373096060694812221)
      ·
        refine ⟨62938185514911022760554583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167835161373096060694812221 62938185514911022760554583)
        ·
          refine ⟨94407278272366534140831875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62938185514911022760554583 94407278272366534140831875)
          ·
            refine ⟨141610917408549801211247813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94407278272366534140831875 141610917408549801211247813)
            ·
              refine ⟨26552047014103087727108965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141610917408549801211247813 26552047014103087727108965)
              ·
                refine ⟨4978508815144328948832931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26552047014103087727108965 4978508815144328948832931)
                ·
                  refine ⟨7467763222716493423249397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4978508815144328948832931 7467763222716493423249397)
                  ·
                    refine ⟨700102802129671258429631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7467763222716493423249397 700102802129671258429631)
                    ·
                      rfl

theorem cell23_4090336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 5].length) (baseStart_4090336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090336 prefixEnd_4090336 := by exact prefixLift 4090336
  have htrace : WordTrace (prefixWord ++ tailWord_4090336) baseStart_4090336 baseEnd_4090336 := by
    simpa [prefixWord, tailWord_4090336, baseEnd_4090336] using wordTrace_append hprefix tailTrace_4090336
  have hstable : (prefixWord ++ tailWord_4090336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090336).length < 2 ^ (prefixWord ++ tailWord_4090336).sum := by decide
  have hdescent : baseEnd_4090336 < baseStart_4090336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090343 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_4090343 : Nat := 118140960795 + 4090343 * 2 ^ 59
def prefixEnd_4090343 : Nat := 4983230072969 + 3 ^ 40 * 4090343 * 2
def baseEnd_4090343 : Nat := 2100312000753595247901361

theorem tailTrace_4090343 : CollatzResearch.WordTrace tailWord_4090343 prefixEnd_4090343 2100312000753595247901361 := by
  unfold tailWord_4090343
  simp only [CollatzResearch.WordTrace]
  refine ⟨149187065420393360813115683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99458043613595573875410455 149187065420393360813115683)
  ·
    refine ⟨223780598130590041219673525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149187065420393360813115683 223780598130590041219673525)
    ·
      refine ⟨20979431074742816364344393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223780598130590041219673525 20979431074742816364344393)
      ·
        refine ⟨15734573306057112273258295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20979431074742816364344393 15734573306057112273258295)
        ·
          refine ⟨23601859959085668409887443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15734573306057112273258295 23601859959085668409887443)
          ·
            refine ⟨35402789938628502614831165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23601859959085668409887443 35402789938628502614831165)
            ·
              refine ⟨13276046226985688480561687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35402789938628502614831165 13276046226985688480561687)
              ·
                refine ⟨19914069340478532720842531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13276046226985688480561687 19914069340478532720842531)
                ·
                  refine ⟨29871104010717799081263797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19914069340478532720842531 29871104010717799081263797)
                  ·
                    refine ⟨2800416001004793663868481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29871104010717799081263797 2800416001004793663868481)
                    ·
                      refine ⟨2100312000753595247901361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800416001004793663868481 2100312000753595247901361)
                      ·
                        rfl

theorem cell23_4090343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_4090343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090343 prefixEnd_4090343 := by exact prefixLift 4090343
  have htrace : WordTrace (prefixWord ++ tailWord_4090343) baseStart_4090343 baseEnd_4090343 := by
    simpa [prefixWord, tailWord_4090343, baseEnd_4090343] using wordTrace_append hprefix tailTrace_4090343
  have hstable : (prefixWord ++ tailWord_4090343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090343).length < 2 ^ (prefixWord ++ tailWord_4090343).sum := by decide
  have hdescent : baseEnd_4090343 < baseStart_4090343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090357 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 6]
def baseStart_4090357 : Nat := 118140960795 + 4090357 * 2 ^ 59
def prefixEnd_4090357 : Nat := 4983230072969 + 3 ^ 40 * 4090357 * 2
def baseEnd_4090357 : Nat := 233368798831417577014033

theorem tailTrace_4090357 : CollatzResearch.WordTrace tailWord_4090357 prefixEnd_4090357 233368798831417577014033 := by
  unfold tailWord_4090357
  simp only [CollatzResearch.WordTrace]
  refine ⟨149187576042342641204125325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99458384028228427469416883 149187576042342641204125325)
  ·
    refine ⟨55945341015878490451546997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149187576042342641204125325 55945341015878490451546997)
    ·
      refine ⟨5244875720238608479832531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55945341015878490451546997 5244875720238608479832531)
      ·
        refine ⟨7867313580357912719748797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5244875720238608479832531 7867313580357912719748797)
        ·
          refine ⟨2950242592634217269905799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7867313580357912719748797 2950242592634217269905799)
          ·
            refine ⟨4425363888951325904858699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950242592634217269905799 4425363888951325904858699)
            ·
              refine ⟨6638045833426988857288049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4425363888951325904858699 6638045833426988857288049)
              ·
                refine ⟨4978534375070241642966037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6638045833426988857288049 4978534375070241642966037)
                ·
                  refine ⟨233368798831417577014033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4978534375070241642966037 233368798831417577014033)
                  ·
                    rfl

theorem cell23_4090357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_4090357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090357 prefixEnd_4090357 := by exact prefixLift 4090357
  have htrace : WordTrace (prefixWord ++ tailWord_4090357) baseStart_4090357 baseEnd_4090357 := by
    simpa [prefixWord, tailWord_4090357, baseEnd_4090357] using wordTrace_append hprefix tailTrace_4090357
  have hstable : (prefixWord ++ tailWord_4090357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090357).length < 2 ^ (prefixWord ++ tailWord_4090357).sum := by decide
  have hdescent : baseEnd_4090357 < baseStart_4090357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090374 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_4090374 : Nat := 118140960795 + 4090374 * 2 ^ 59
def prefixEnd_4090374 : Nat := 4983230072969 + 3 ^ 40 * 4090374 * 2
def baseEnd_4090374 : Nat := 233369768739320514068191

theorem tailTrace_4090374 : CollatzResearch.WordTrace tailWord_4090374 prefixEnd_4090374 233369768739320514068191 := by
  unfold tailWord_4090374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662131127602532909609193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99458797388854035404996117 4662131127602532909609193)
  ·
    refine ⟨3496598345701899682206895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4662131127602532909609193 3496598345701899682206895)
    ·
      refine ⟨5244897518552849523310343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3496598345701899682206895 5244897518552849523310343)
      ·
        refine ⟨7867346277829274284965515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5244897518552849523310343 7867346277829274284965515)
        ·
          refine ⟨11801019416743911427448273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7867346277829274284965515 11801019416743911427448273)
          ·
            refine ⟨8850764562557933570586205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11801019416743911427448273 8850764562557933570586205)
            ·
              refine ⟨3319036710959225088969827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8850764562557933570586205 3319036710959225088969827)
              ·
                refine ⟨4978555066438837633454741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319036710959225088969827 4978555066438837633454741)
                ·
                  refine ⟨233369768739320514068191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4978555066438837633454741 233369768739320514068191)
                  ·
                    rfl

theorem cell23_4090374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_4090374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090374 prefixEnd_4090374 := by exact prefixLift 4090374
  have htrace : WordTrace (prefixWord ++ tailWord_4090374) baseStart_4090374 baseEnd_4090374 := by
    simpa [prefixWord, tailWord_4090374, baseEnd_4090374] using wordTrace_append hprefix tailTrace_4090374
  have hstable : (prefixWord ++ tailWord_4090374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090374).length < 2 ^ (prefixWord ++ tailWord_4090374).sum := by decide
  have hdescent : baseEnd_4090374 < baseStart_4090374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090396 : List Nat := [2, 2, 3, 1, 2, 3, 1, 9]
def baseStart_4090396 : Nat := 118140960795 + 4090396 * 2 ^ 59
def prefixEnd_4090396 : Nat := 4983230072969 + 3 ^ 40 * 4090396 * 2
def baseEnd_4090396 : Nat := 77790341304751242242171

theorem tailTrace_4090396 : CollatzResearch.WordTrace tailWord_4090396 prefixEnd_4090396 77790341304751242242171 := by
  unfold tailWord_4090396
  simp only [CollatzResearch.WordTrace]
  refine ⟨74594499244600675432397521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99459332326134233909863361 74594499244600675432397521)
  ·
    refine ⟨55945874433450506574298141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74594499244600675432397521 55945874433450506574298141)
    ·
      refine ⟨20979702912543939965361803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55945874433450506574298141 20979702912543939965361803)
      ·
        refine ⟨31469554368815909948042705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20979702912543939965361803 31469554368815909948042705)
        ·
          refine ⟨23602165776611932461032029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31469554368815909948042705 23602165776611932461032029)
          ·
            refine ⟨8850812166229474672887011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23602165776611932461032029 8850812166229474672887011)
            ·
              refine ⟨13276218249344212009330517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8850812166229474672887011 13276218249344212009330517)
              ·
                refine ⟨77790341304751242242171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13276218249344212009330517 77790341304751242242171)
                ·
                  rfl

theorem cell23_4090396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 9].length) (baseStart_4090396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090396 prefixEnd_4090396 := by exact prefixLift 4090396
  have htrace : WordTrace (prefixWord ++ tailWord_4090396) baseStart_4090396 baseEnd_4090396 := by
    simpa [prefixWord, tailWord_4090396, baseEnd_4090396] using wordTrace_append hprefix tailTrace_4090396
  have hstable : (prefixWord ++ tailWord_4090396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090396).length < 2 ^ (prefixWord ++ tailWord_4090396).sum := by decide
  have hdescent : baseEnd_4090396 < baseStart_4090396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090410 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_4090410 : Nat := 118140960795 + 4090410 * 2 ^ 59
def prefixEnd_4090410 : Nat := 4983230072969 + 3 ^ 40 * 4090410 * 2
def baseEnd_4090410 : Nat := 2100346403957446485763553

theorem tailTrace_4090410 : CollatzResearch.WordTrace tailWord_4090410 prefixEnd_4090410 2100346403957446485763553 := by
  unfold tailWord_4090410
  simp only [CollatzResearch.WordTrace]
  refine ⟨37297377277787657813951171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99459672740767087503869789 37297377277787657813951171)
  ·
    refine ⟨55946065916681486720926757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37297377277787657813951171 55946065916681486720926757)
    ·
      refine ⟨10489887359377778760173767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55946065916681486720926757 10489887359377778760173767)
      ·
        refine ⟨15734831039066668140260651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10489887359377778760173767 15734831039066668140260651)
        ·
          refine ⟨23602246558600002210390977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15734831039066668140260651 23602246558600002210390977)
          ·
            refine ⟨17701684918950001657793233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23602246558600002210390977 17701684918950001657793233)
            ·
              refine ⟨13276263689212501243344925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17701684918950001657793233 13276263689212501243344925)
              ·
                refine ⟨4978598883454687966254347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13276263689212501243344925 4978598883454687966254347)
                ·
                  refine ⟨7467898325182031949381521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4978598883454687966254347 7467898325182031949381521)
                  ·
                    refine ⟨5600923743886523962036141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7467898325182031949381521 5600923743886523962036141)
                    ·
                      refine ⟨2100346403957446485763553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5600923743886523962036141 2100346403957446485763553)
                      ·
                        rfl

theorem cell23_4090410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_4090410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090410 prefixEnd_4090410 := by exact prefixLift 4090410
  have htrace : WordTrace (prefixWord ++ tailWord_4090410) baseStart_4090410 baseEnd_4090410 := by
    simpa [prefixWord, tailWord_4090410, baseEnd_4090410] using wordTrace_append hprefix tailTrace_4090410
  have hstable : (prefixWord ++ tailWord_4090410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090410).length < 2 ^ (prefixWord ++ tailWord_4090410).sum := by decide
  have hdescent : baseEnd_4090410 < baseStart_4090410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090423 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 4, 1, 3]
def baseStart_4090423 : Nat := 118140960795 + 4090423 * 2 ^ 59
def prefixEnd_4090423 : Nat := 4983230072969 + 3 ^ 40 * 4090423 * 2
def baseEnd_4090423 : Nat := 2100353079205954934900993

theorem tailTrace_4090423 : CollatzResearch.WordTrace tailWord_4090423 prefixEnd_4090423 2100353079205954934900993 := by
  unfold tailWord_4090423
  simp only [CollatzResearch.WordTrace]
  refine ⟨149189983260103534476027923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99459988840069022984018615 149189983260103534476027923)
  ·
    refine ⟨223784974890155301714041885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149189983260103534476027923 223784974890155301714041885)
    ·
      refine ⟨83919365583808238142765707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223784974890155301714041885 83919365583808238142765707)
      ·
        refine ⟨125879048375712357214148561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83919365583808238142765707 125879048375712357214148561)
        ·
          refine ⟨94409286281784267910611421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125879048375712357214148561 94409286281784267910611421)
          ·
            refine ⟨35403482355669100466479283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94409286281784267910611421 35403482355669100466479283)
            ·
              refine ⟨53105223533503650699718925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35403482355669100466479283 53105223533503650699718925)
              ·
                refine ⟨19914458825063869012394597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53105223533503650699718925 19914458825063869012394597)
                ·
                  refine ⟨3733961029699475439823987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19914458825063869012394597 3733961029699475439823987)
                  ·
                    refine ⟨5600941544549213159735981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3733961029699475439823987 5600941544549213159735981)
                    ·
                      refine ⟨2100353079205954934900993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5600941544549213159735981 2100353079205954934900993)
                      ·
                        rfl

theorem cell23_4090423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_4090423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090423 prefixEnd_4090423 := by exact prefixLift 4090423
  have htrace : WordTrace (prefixWord ++ tailWord_4090423) baseStart_4090423 baseEnd_4090423 := by
    simpa [prefixWord, tailWord_4090423, baseEnd_4090423] using wordTrace_append hprefix tailTrace_4090423
  have hstable : (prefixWord ++ tailWord_4090423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090423).length < 2 ^ (prefixWord ++ tailWord_4090423).sum := by decide
  have hdescent : baseEnd_4090423 < baseStart_4090423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090424 : List Nat := [2, 1, 2, 1, 4, 1, 5, 2, 1, 2, 2]
def baseStart_4090424 : Nat := 118140960795 + 4090424 * 2 ^ 59
def prefixEnd_4090424 : Nat := 4983230072969 + 3 ^ 40 * 4090424 * 2
def baseEnd_4090424 : Nat := 2100353592686609430988489

theorem tailTrace_4090424 : CollatzResearch.WordTrace tailWord_4090424 prefixEnd_4090424 2100353592686609430988489 := by
  unfold tailWord_4090424
  simp only [CollatzResearch.WordTrace]
  refine ⟨74595009866549955823407163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99460013155399941097876217 74595009866549955823407163)
  ·
    refine ⟨111892514799824933735110745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74595009866549955823407163 111892514799824933735110745)
    ·
      refine ⟨83919386099868700301333059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111892514799824933735110745 83919386099868700301333059)
      ·
        refine ⟨125879079149803050451999589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83919386099868700301333059 125879079149803050451999589)
        ·
          refine ⟨23602327340588071959749923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125879079149803050451999589 23602327340588071959749923)
          ·
            refine ⟨35403491010882107939624885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23602327340588071959749923 35403491010882107939624885)
            ·
              refine ⟨3319077282270197619339833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35403491010882107939624885 3319077282270197619339833)
              ·
                refine ⟨2489307961702648214504875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3319077282270197619339833 2489307961702648214504875)
                ·
                  refine ⟨3733961942553972321757313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2489307961702648214504875 3733961942553972321757313)
                  ·
                    refine ⟨2800471456915479241317985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3733961942553972321757313 2800471456915479241317985)
                    ·
                      refine ⟨2100353592686609430988489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800471456915479241317985 2100353592686609430988489)
                      ·
                        rfl

theorem cell23_4090424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 1, 2, 2].length) (baseStart_4090424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090424 prefixEnd_4090424 := by exact prefixLift 4090424
  have htrace : WordTrace (prefixWord ++ tailWord_4090424) baseStart_4090424 baseEnd_4090424 := by
    simpa [prefixWord, tailWord_4090424, baseEnd_4090424] using wordTrace_append hprefix tailTrace_4090424
  have hstable : (prefixWord ++ tailWord_4090424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090424).length < 2 ^ (prefixWord ++ tailWord_4090424).sum := by decide
  have hdescent : baseEnd_4090424 < baseStart_4090424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090430 : List Nat := [4, 2, 1, 4, 1, 1, 2, 8]
def baseStart_4090430 : Nat := 118140960795 + 4090430 * 2 ^ 59
def prefixEnd_4090430 : Nat := 4983230072969 + 3 ^ 40 * 4090430 * 2
def baseEnd_4090430 : Nat := 77790987910019866944943

theorem tailTrace_4090430 : CollatzResearch.WordTrace tailWord_4090430 prefixEnd_4090430 77790987910019866944943 := by
  unfold tailWord_4090430
  simp only [CollatzResearch.WordTrace]
  refine ⟨18648779821384771833941593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99460159047385449781021829 18648779821384771833941593)
  ·
    refine ⟨13986584866038578875456195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18648779821384771833941593 13986584866038578875456195)
    ·
      refine ⟨20979877299057868313184293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13986584866038578875456195 20979877299057868313184293)
      ·
        refine ⟨3933726993573350308722055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20979877299057868313184293 3933726993573350308722055)
        ·
          refine ⟨5900590490360025463083083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3933726993573350308722055 5900590490360025463083083)
          ·
            refine ⟨8850885735540038194624625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5900590490360025463083083 8850885735540038194624625)
            ·
              refine ⟨6638164301655028645968469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8850885735540038194624625 6638164301655028645968469)
              ·
                refine ⟨77790987910019866944943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6638164301655028645968469 77790987910019866944943)
                ·
                  rfl

theorem cell23_4090430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_4090430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090430 prefixEnd_4090430 := by exact prefixLift 4090430
  have htrace : WordTrace (prefixWord ++ tailWord_4090430) baseStart_4090430 baseEnd_4090430 := by
    simpa [prefixWord, tailWord_4090430, baseEnd_4090430] using wordTrace_append hprefix tailTrace_4090430
  have hstable : (prefixWord ++ tailWord_4090430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090430).length < 2 ^ (prefixWord ++ tailWord_4090430).sum := by decide
  have hdescent : baseEnd_4090430 < baseStart_4090430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090450 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_4090450 : Nat := 118140960795 + 4090450 * 2 ^ 59
def prefixEnd_4090450 : Nat := 4983230072969 + 3 ^ 40 * 4090450 * 2
def baseEnd_4090450 : Nat := 2100366943183626329263369

theorem tailTrace_4090450 : CollatzResearch.WordTrace tailWord_4090450 prefixEnd_4090450 2100366943183626329263369 := by
  unfold tailWord_4090450
  simp only [CollatzResearch.WordTrace]
  refine ⟨37297742007751429521815201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99460645354003812058173869 37297742007751429521815201)
  ·
    refine ⟨27973306505813572141361401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37297742007751429521815201 27973306505813572141361401)
    ·
      refine ⟨20979979879360179106021051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27973306505813572141361401 20979979879360179106021051)
      ·
        refine ⟨31469969819040268659031577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20979979879360179106021051 31469969819040268659031577)
        ·
          refine ⟨23602477364280201494273683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31469969819040268659031577 23602477364280201494273683)
          ·
            refine ⟨35403716046420302241410525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23602477364280201494273683 35403716046420302241410525)
            ·
              refine ⟨13276393517407613340528947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35403716046420302241410525 13276393517407613340528947)
              ·
                refine ⟨19914590276111420010793421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13276393517407613340528947 19914590276111420010793421)
                ·
                  refine ⟨7467971353541782504047533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19914590276111420010793421 7467971353541782504047533)
                  ·
                    refine ⟨2800489257578168439017825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7467971353541782504047533 2800489257578168439017825)
                    ·
                      refine ⟨2100366943183626329263369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800489257578168439017825 2100366943183626329263369)
                      ·
                        rfl

theorem cell23_4090450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_4090450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090450 prefixEnd_4090450 := by exact prefixLift 4090450
  have htrace : WordTrace (prefixWord ++ tailWord_4090450) baseStart_4090450 baseEnd_4090450 := by
    simpa [prefixWord, tailWord_4090450, baseEnd_4090450] using wordTrace_append hprefix tailTrace_4090450
  have hstable : (prefixWord ++ tailWord_4090450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090450).length < 2 ^ (prefixWord ++ tailWord_4090450).sum := by decide
  have hdescent : baseEnd_4090450 < baseStart_4090450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090467 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 1, 3, 2]
def baseStart_4090467 : Nat := 118140960795 + 4090467 * 2 ^ 59
def prefixEnd_4090467 : Nat := 4983230072969 + 3 ^ 40 * 4090467 * 2
def baseEnd_4090467 : Nat := 2100375672354752762750791

theorem tailTrace_4090467 : CollatzResearch.WordTrace tailWord_4090467 prefixEnd_4090467 2100375672354752762750791 := by
  unfold tailWord_4090467
  simp only [CollatzResearch.WordTrace]
  refine ⟨149191588071944129990629655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99461058714629419993753103 149191588071944129990629655)
  ·
    refine ⟨223787382107916194985944483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149191588071944129990629655 223787382107916194985944483)
    ·
      refine ⟨335681073161874292478916725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223787382107916194985944483 335681073161874292478916725)
      ·
        refine ⟨31470100608925714919898443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335681073161874292478916725 31470100608925714919898443)
        ·
          refine ⟨47205150913388572379847665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31470100608925714919898443 47205150913388572379847665)
          ·
            refine ⟨35403863185041429284885749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47205150913388572379847665 35403863185041429284885749)
            ·
              refine ⟨3319112173597633995458039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35403863185041429284885749 3319112173597633995458039)
              ·
                refine ⟨4978668260396450993187059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319112173597633995458039 4978668260396450993187059)
                ·
                  refine ⟨7468002390594676489780589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4978668260396450993187059 7468002390594676489780589)
                  ·
                    refine ⟨2800500896473003683667721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7468002390594676489780589 2800500896473003683667721)
                    ·
                      refine ⟨2100375672354752762750791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800500896473003683667721 2100375672354752762750791)
                      ·
                        rfl

theorem cell23_4090467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_4090467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090467 prefixEnd_4090467 := by exact prefixLift 4090467
  have htrace : WordTrace (prefixWord ++ tailWord_4090467) baseStart_4090467 baseEnd_4090467 := by
    simpa [prefixWord, tailWord_4090467, baseEnd_4090467] using wordTrace_append hprefix tailTrace_4090467
  have hstable : (prefixWord ++ tailWord_4090467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090467).length < 2 ^ (prefixWord ++ tailWord_4090467).sum := by decide
  have hdescent : baseEnd_4090467 < baseStart_4090467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090497 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_4090497 : Nat := 118140960795 + 4090497 * 2 ^ 59
def prefixEnd_4090497 : Nat := 4983230072969 + 3 ^ 40 * 4090497 * 2
def baseEnd_4090497 : Nat := 2100391076774387645375653

theorem tailTrace_4090497 : CollatzResearch.WordTrace tailWord_4090497 prefixEnd_4090497 2100391076774387645375653 := by
  unfold tailWord_4090497
  simp only [CollatzResearch.WordTrace]
  refine ⟨149192682261835445114221745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99461788174556963409481163 149192682261835445114221745)
  ·
    refine ⟨111894511696376583835666309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149192682261835445114221745 111894511696376583835666309)
    ·
      refine ⟨20980220943070609469187433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111894511696376583835666309 20980220943070609469187433)
      ·
        refine ⟨15735165707302957101890575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20980220943070609469187433 15735165707302957101890575)
        ·
          refine ⟨23602748560954435652835863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15735165707302957101890575 23602748560954435652835863)
          ·
            refine ⟨35404122841431653479253795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23602748560954435652835863 35404122841431653479253795)
            ·
              refine ⟨53106184262147480218880693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35404122841431653479253795 53106184262147480218880693)
              ·
                refine ⟨4978704774576326270520065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53106184262147480218880693 4978704774576326270520065)
                ·
                  refine ⟨3734028580932244702890049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4978704774576326270520065 3734028580932244702890049)
                  ·
                    refine ⟨2800521435699183527167537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3734028580932244702890049 2800521435699183527167537)
                    ·
                      refine ⟨2100391076774387645375653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800521435699183527167537 2100391076774387645375653)
                      ·
                        rfl

theorem cell23_4090497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_4090497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090497 prefixEnd_4090497 := by exact prefixLift 4090497
  have htrace : WordTrace (prefixWord ++ tailWord_4090497) baseStart_4090497 baseEnd_4090497 := by
    simpa [prefixWord, tailWord_4090497, baseEnd_4090497] using wordTrace_append hprefix tailTrace_4090497
  have hstable : (prefixWord ++ tailWord_4090497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090497).length < 2 ^ (prefixWord ++ tailWord_4090497).sum := by decide
  have hdescent : baseEnd_4090497 < baseStart_4090497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090520 : List Nat := [2, 1, 2, 4, 1, 1, 4, 3, 5]
def baseStart_4090520 : Nat := 118140960795 + 4090520 * 2 ^ 59
def prefixEnd_4090520 : Nat := 4983230072969 + 3 ^ 40 * 4090520 * 2
def baseEnd_4090520 : Nat := 233378098536604561709783

theorem tailTrace_4090520 : CollatzResearch.WordTrace tailWord_4090520 prefixEnd_4090520 233378098536604561709783 := by
  unfold tailWord_4090520
  simp only [CollatzResearch.WordTrace]
  refine ⟨74596760570376060021154507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99462347427168080028206009 74596760570376060021154507)
  ·
    refine ⟨111895140855564090031731761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74596760570376060021154507 111895140855564090031731761)
    ·
      refine ⟨83921355641673067523798821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111895140855564090031731761 83921355641673067523798821)
      ·
        refine ⟨15735254182813700160712279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83921355641673067523798821 15735254182813700160712279)
        ·
          refine ⟨23602881274220550241068419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15735254182813700160712279 23602881274220550241068419)
          ·
            refine ⟨35404321911330825361602629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23602881274220550241068419 35404321911330825361602629)
            ·
              refine ⟨6638310358374529755300493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35404321911330825361602629 6638310358374529755300493)
              ·
                refine ⟨2489366384390448658237685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6638310358374529755300493 2489366384390448658237685)
                ·
                  refine ⟨233378098536604561709783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2489366384390448658237685 233378098536604561709783)
                  ·
                    rfl

theorem cell23_4090520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 5].length) (baseStart_4090520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090520 prefixEnd_4090520 := by exact prefixLift 4090520
  have htrace : WordTrace (prefixWord ++ tailWord_4090520) baseStart_4090520 baseEnd_4090520 := by
    simpa [prefixWord, tailWord_4090520, baseEnd_4090520] using wordTrace_append hprefix tailTrace_4090520
  have hstable : (prefixWord ++ tailWord_4090520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090520).length < 2 ^ (prefixWord ++ tailWord_4090520).sum := by decide
  have hdescent : baseEnd_4090520 < baseStart_4090520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090593 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 8]
def baseStart_4090593 : Nat := 118140960795 + 4090593 * 2 ^ 59
def prefixEnd_4090593 : Nat := 4983230072969 + 3 ^ 40 * 4090593 * 2
def baseEnd_4090593 : Nat := 233382263435246585530579

theorem tailTrace_4090593 : CollatzResearch.WordTrace tailWord_4090593 prefixEnd_4090593 233382263435246585530579 := by
  unfold tailWord_4090593
  simp only [CollatzResearch.WordTrace]
  refine ⟨149196183669487653509716433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99464122446325102339810955 149196183669487653509716433)
  ·
    refine ⟨111897137752115740132287325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149196183669487653509716433 111897137752115740132287325)
    ·
      refine ⟨41961426657043402549607747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111897137752115740132287325 41961426657043402549607747)
      ·
        refine ⟨62942139985565103824411621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41961426657043402549607747 62942139985565103824411621)
        ·
          refine ⟨11801651247293456967077179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62942139985565103824411621 11801651247293456967077179)
          ·
            refine ⟨17702476870940185450615769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11801651247293456967077179 17702476870940185450615769)
            ·
              refine ⟨13276857653205139087961827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17702476870940185450615769 13276857653205139087961827)
              ·
                refine ⟨19915286479807708631942741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13276857653205139087961827 19915286479807708631942741)
                ·
                  refine ⟨233382263435246585530579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19915286479807708631942741 233382263435246585530579)
                  ·
                    rfl

theorem cell23_4090593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 8].length) (baseStart_4090593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090593 prefixEnd_4090593 := by exact prefixLift 4090593
  have htrace : WordTrace (prefixWord ++ tailWord_4090593) baseStart_4090593 baseEnd_4090593 := by
    simpa [prefixWord, tailWord_4090593, baseEnd_4090593] using wordTrace_append hprefix tailTrace_4090593
  have hstable : (prefixWord ++ tailWord_4090593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090593).length < 2 ^ (prefixWord ++ tailWord_4090593).sum := by decide
  have hdescent : baseEnd_4090593 < baseStart_4090593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090597 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 3, 4]
def baseStart_4090597 : Nat := 118140960795 + 4090597 * 2 ^ 59
def prefixEnd_4090597 : Nat := 4983230072969 + 3 ^ 40 * 4090597 * 2
def baseEnd_4090597 : Nat := 700147474946612418041731

theorem tailTrace_4090597 : CollatzResearch.WordTrace tailWord_4090597 prefixEnd_4090597 700147474946612418041731 := by
  unfold tailWord_4090597
  simp only [CollatzResearch.WordTrace]
  refine ⟨149196329561473162192862045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99464219707648774795241363 149196329561473162192862045)
  ·
    refine ⟨55948623585552435822323267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149196329561473162192862045 55948623585552435822323267)
    ·
      refine ⟨83922935378328653733484901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55948623585552435822323267 83922935378328653733484901)
      ·
        refine ⟨15735550383436622575028419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83922935378328653733484901 15735550383436622575028419)
        ·
          refine ⟨23603325575154933862542629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15735550383436622575028419 23603325575154933862542629)
          ·
            refine ⟨4425623545341550099226743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23603325575154933862542629 4425623545341550099226743)
            ·
              refine ⟨6638435318012325148840115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4425623545341550099226743 6638435318012325148840115)
              ·
                refine ⟨9957652977018487723260173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6638435318012325148840115 9957652977018487723260173)
                ·
                  refine ⟨3734119866381932896222565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9957652977018487723260173 3734119866381932896222565)
                  ·
                    refine ⟨700147474946612418041731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3734119866381932896222565 700147474946612418041731)
                    ·
                      rfl

theorem cell23_4090597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_4090597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090597 prefixEnd_4090597 := by exact prefixLift 4090597
  have htrace : WordTrace (prefixWord ++ tailWord_4090597) baseStart_4090597 baseEnd_4090597 := by
    simpa [prefixWord, tailWord_4090597, baseEnd_4090597] using wordTrace_append hprefix tailTrace_4090597
  have hstable : (prefixWord ++ tailWord_4090597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090597).length < 2 ^ (prefixWord ++ tailWord_4090597).sum := by decide
  have hdescent : baseEnd_4090597 < baseStart_4090597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090610 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 6]
def baseStart_4090610 : Nat := 118140960795 + 4090610 * 2 ^ 59
def prefixEnd_4090610 : Nat := 4983230072969 + 3 ^ 40 * 4090610 * 2
def baseEnd_4090610 : Nat := 233383233343149522584737

theorem tailTrace_4090610 : CollatzResearch.WordTrace tailWord_4090610 prefixEnd_4090610 233383233343149522584737 := by
  unfold tailWord_4090610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37299200927606516353271321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99464535806950710275390189 37299200927606516353271321)
  ·
    refine ⟨27974400695704887264953491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37299200927606516353271321 27974400695704887264953491)
    ·
      refine ⟨41961601043557330897430237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27974400695704887264953491 41961601043557330897430237)
      ·
        refine ⟨15735600391333999086536339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41961601043557330897430237 15735600391333999086536339)
        ·
          refine ⟨23603400587000998629804509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15735600391333999086536339 23603400587000998629804509)
          ·
            refine ⟨8851275220125374486176691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23603400587000998629804509 8851275220125374486176691)
            ·
              refine ⟨13276912830188061729265037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851275220125374486176691 13276912830188061729265037)
              ·
                refine ⟨4978842311320523148474389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13276912830188061729265037 4978842311320523148474389)
                ·
                  refine ⟨233383233343149522584737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4978842311320523148474389 233383233343149522584737)
                  ·
                    rfl

theorem cell23_4090610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_4090610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090610 prefixEnd_4090610 := by exact prefixLift 4090610
  have htrace : WordTrace (prefixWord ++ tailWord_4090610) baseStart_4090610 baseEnd_4090610 := by
    simpa [prefixWord, tailWord_4090610, baseEnd_4090610] using wordTrace_append hprefix tailTrace_4090610
  have hstable : (prefixWord ++ tailWord_4090610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090610).length < 2 ^ (prefixWord ++ tailWord_4090610).sum := by decide
  have hdescent : baseEnd_4090610 < baseStart_4090610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090680 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 3, 2, 3]
def baseStart_4090680 : Nat := 118140960795 + 4090680 * 2 ^ 59
def prefixEnd_4090680 : Nat := 4983230072969 + 3 ^ 40 * 4090680 * 2
def baseEnd_4090680 : Nat := 2100485043734160429387311

theorem tailTrace_4090680 : CollatzResearch.WordTrace tailWord_4090680 prefixEnd_4090680 2100485043734160429387311 := by
  unfold tailWord_4090680
  simp only [CollatzResearch.WordTrace]
  refine ⟨74599678410086233684066747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99466237880114978245422329 74599678410086233684066747)
  ·
    refine ⟨111899517615129350526100121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74599678410086233684066747 111899517615129350526100121)
    ·
      refine ⟨83924638211347012894575091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111899517615129350526100121 83924638211347012894575091)
      ·
        refine ⟨125886957317020519341862637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83924638211347012894575091 125886957317020519341862637)
        ·
          refine ⟨47207608993882694753198489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125886957317020519341862637 47207608993882694753198489)
          ·
            refine ⟨35405706745412021064898867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47207608993882694753198489 35405706745412021064898867)
            ·
              refine ⟨53108560118118031597348301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35405706745412021064898867 53108560118118031597348301)
              ·
                refine ⟨19915710044294261849005613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53108560118118031597348301 19915710044294261849005613)
                ·
                  refine ⟨7468391266610348193377105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19915710044294261849005613 7468391266610348193377105)
                  ·
                    refine ⟨5601293449957761145032829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7468391266610348193377105 5601293449957761145032829)
                    ·
                      refine ⟨2100485043734160429387311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5601293449957761145032829 2100485043734160429387311)
                      ·
                        rfl

theorem cell23_4090680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_4090680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090680 prefixEnd_4090680 := by exact prefixLift 4090680
  have htrace : WordTrace (prefixWord ++ tailWord_4090680) baseStart_4090680 baseEnd_4090680 := by
    simpa [prefixWord, tailWord_4090680, baseEnd_4090680] using wordTrace_append hprefix tailTrace_4090680
  have hstable : (prefixWord ++ tailWord_4090680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090680).length < 2 ^ (prefixWord ++ tailWord_4090680).sum := by decide
  have hdescent : baseEnd_4090680 < baseStart_4090680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090697 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 1, 2, 3]
def baseStart_4090697 : Nat := 118140960795 + 4090697 * 2 ^ 59
def prefixEnd_4090697 : Nat := 4983230072969 + 3 ^ 40 * 4090697 * 2
def baseEnd_4090697 : Nat := 2100493772905286862874733

theorem tailTrace_4090697 : CollatzResearch.WordTrace tailWord_4090697 prefixEnd_4090697 2100493772905286862874733 := by
  unfold tailWord_4090697
  simp only [CollatzResearch.WordTrace]
  refine ⟨149199976861110879271502345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99466651240740586181001563 149199976861110879271502345)
  ·
    refine ⟨111899982645833159453626759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149199976861110879271502345 111899982645833159453626759)
    ·
      refine ⟨167849973968749739180440139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111899982645833159453626759 167849973968749739180440139)
      ·
        refine ⟨251774960953124608770660209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167849973968749739180440139 251774960953124608770660209)
        ·
          refine ⟨188831220714843456577995157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251774960953124608770660209 188831220714843456577995157)
          ·
            refine ⟨8851463471008287027093523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188831220714843456577995157 8851463471008287027093523)
            ·
              refine ⟨13277195206512430540640285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851463471008287027093523 13277195206512430540640285)
              ·
                refine ⟨4978948202442161452740107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13277195206512430540640285 4978948202442161452740107)
                ·
                  refine ⟨7468422303663242179110161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4978948202442161452740107 7468422303663242179110161)
                  ·
                    refine ⟨5601316727747431634332621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7468422303663242179110161 5601316727747431634332621)
                    ·
                      refine ⟨2100493772905286862874733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5601316727747431634332621 2100493772905286862874733)
                      ·
                        rfl

theorem cell23_4090697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 2, 3].length) (baseStart_4090697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090697 prefixEnd_4090697 := by exact prefixLift 4090697
  have htrace : WordTrace (prefixWord ++ tailWord_4090697) baseStart_4090697 baseEnd_4090697 := by
    simpa [prefixWord, tailWord_4090697, baseEnd_4090697] using wordTrace_append hprefix tailTrace_4090697
  have hstable : (prefixWord ++ tailWord_4090697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090697).length < 2 ^ (prefixWord ++ tailWord_4090697).sum := by decide
  have hdescent : baseEnd_4090697 < baseStart_4090697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090711 : List Nat := [1, 1, 3, 2, 4, 1, 2, 4, 1, 2, 2]
def baseStart_4090711 : Nat := 118140960795 + 4090711 * 2 ^ 59
def prefixEnd_4090711 : Nat := 4983230072969 + 3 ^ 40 * 4090711 * 2
def baseEnd_4090711 : Nat := 2100500961634449808099669

theorem tailTrace_4090711 : CollatzResearch.WordTrace tailWord_4090711 prefixEnd_4090711 2100500961634449808099669 := by
  unfold tailWord_4090711
  simp only [CollatzResearch.WordTrace]
  refine ⟨149200487483060159662511987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99466991655373439775007991 149200487483060159662511987)
  ·
    refine ⟨223800731224590239493767981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149200487483060159662511987 223800731224590239493767981)
    ·
      refine ⟨83925274209221339810162993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223800731224590239493767981 83925274209221339810162993)
      ·
        refine ⟨62943955656916004857622245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83925274209221339810162993 62943955656916004857622245)
        ·
          refine ⟨11801991685671750910804171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62943955656916004857622245 11801991685671750910804171)
          ·
            refine ⟨17702987528507626366206257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11801991685671750910804171 17702987528507626366206257)
            ·
              refine ⟨13277240646380719774654693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17702987528507626366206257 13277240646380719774654693)
              ·
                refine ⟨2489482621196384957747755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13277240646380719774654693 2489482621196384957747755)
                ·
                  refine ⟨3734223931794577436621633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2489482621196384957747755 3734223931794577436621633)
                  ·
                    refine ⟨2800667948845933077466225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3734223931794577436621633 2800667948845933077466225)
                    ·
                      refine ⟨2100500961634449808099669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800667948845933077466225 2100500961634449808099669)
                      ·
                        rfl

theorem cell23_4090711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_4090711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090711 prefixEnd_4090711 := by exact prefixLift 4090711
  have htrace : WordTrace (prefixWord ++ tailWord_4090711) baseStart_4090711 baseEnd_4090711 := by
    simpa [prefixWord, tailWord_4090711, baseEnd_4090711] using wordTrace_append hprefix tailTrace_4090711
  have hstable : (prefixWord ++ tailWord_4090711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090711).length < 2 ^ (prefixWord ++ tailWord_4090711).sum := by decide
  have hdescent : baseEnd_4090711 < baseStart_4090711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090727 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_4090727 : Nat := 118140960795 + 4090727 * 2 ^ 59
def prefixEnd_4090727 : Nat := 4983230072969 + 3 ^ 40 * 4090727 * 2
def baseEnd_4090727 : Nat := 2100509177324921745499595

theorem tailTrace_4090727 : CollatzResearch.WordTrace tailWord_4090727 prefixEnd_4090727 2100509177324921745499595 := by
  unfold tailWord_4090727
  simp only [CollatzResearch.WordTrace]
  refine ⟨149201071051002194395094435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99467380700668129596729623 149201071051002194395094435)
  ·
    refine ⟨223801606576503291592641653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149201071051002194395094435 223801606576503291592641653)
    ·
      refine ⟨20981400616547183586810155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223801606576503291592641653 20981400616547183586810155)
      ·
        refine ⟨31472100924820775380215233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20981400616547183586810155 31472100924820775380215233)
        ·
          refine ⟨23604075693615581535161425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31472100924820775380215233 23604075693615581535161425)
          ·
            refine ⟨17703056770211686151371069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23604075693615581535161425 17703056770211686151371069)
            ·
              refine ⟨6638646288829382306764151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17703056770211686151371069 6638646288829382306764151)
              ·
                refine ⟨9957969433244073460146227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6638646288829382306764151 9957969433244073460146227)
                ·
                  refine ⟨14936954149866110190219341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9957969433244073460146227 14936954149866110190219341)
                  ·
                    refine ⟨5601357806199791321332253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14936954149866110190219341 5601357806199791321332253)
                    ·
                      refine ⟨2100509177324921745499595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5601357806199791321332253 2100509177324921745499595)
                      ·
                        rfl

theorem cell23_4090727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_4090727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090727 prefixEnd_4090727 := by exact prefixLift 4090727
  have htrace : WordTrace (prefixWord ++ tailWord_4090727) baseStart_4090727 baseEnd_4090727 := by
    simpa [prefixWord, tailWord_4090727, baseEnd_4090727] using wordTrace_append hprefix tailTrace_4090727
  have hstable : (prefixWord ++ tailWord_4090727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090727).length < 2 ^ (prefixWord ++ tailWord_4090727).sum := by decide
  have hdescent : baseEnd_4090727 < baseStart_4090727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090734 : List Nat := [4, 1, 2, 3, 2, 2, 2, 7]
def baseStart_4090734 : Nat := 118140960795 + 4090734 * 2 ^ 59
def prefixEnd_4090734 : Nat := 4983230072969 + 3 ^ 40 * 4090734 * 2
def baseEnd_4090734 : Nat := 77796769321833452522669

theorem tailTrace_4090734 : CollatzResearch.WordTrace tailWord_4090734 prefixEnd_4090734 77796769321833452522669 := by
  unfold tailWord_4090734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18650165795247104323824907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99467550907984556393732837 18650165795247104323824907)
  ·
    refine ⟨27975248692870656485737361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18650165795247104323824907 27975248692870656485737361)
    ·
      refine ⟨20981436519652992364303021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27975248692870656485737361 20981436519652992364303021)
      ·
        refine ⟨7868038694869872136613633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20981436519652992364303021 7868038694869872136613633)
        ·
          refine ⟨5901029021152404102460225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7868038694869872136613633 5901029021152404102460225)
          ·
            refine ⟨4425771765864303076845169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5901029021152404102460225 4425771765864303076845169)
            ·
              refine ⟨3319328824398227307633877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4425771765864303076845169 3319328824398227307633877)
              ·
                refine ⟨77796769321833452522669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3319328824398227307633877 77796769321833452522669)
                ·
                  rfl

theorem cell23_4090734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_4090734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090734 prefixEnd_4090734 := by exact prefixLift 4090734
  have htrace : WordTrace (prefixWord ++ tailWord_4090734) baseStart_4090734 baseEnd_4090734 := by
    simpa [prefixWord, tailWord_4090734, baseEnd_4090734] using wordTrace_append hprefix tailTrace_4090734
  have hstable : (prefixWord ++ tailWord_4090734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090734).length < 2 ^ (prefixWord ++ tailWord_4090734).sum := by decide
  have hdescent : baseEnd_4090734 < baseStart_4090734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090743 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 1, 8]
def baseStart_4090743 : Nat := 118140960795 + 4090743 * 2 ^ 59
def prefixEnd_4090743 : Nat := 4983230072969 + 3 ^ 40 * 4090743 * 2
def baseEnd_4090743 : Nat := 700172464338464560966507

theorem tailTrace_4090743 : CollatzResearch.WordTrace tailWord_4090743 prefixEnd_4090743 700172464338464560966507 := by
  unfold tailWord_4090743
  simp only [CollatzResearch.WordTrace]
  refine ⟨149201654618944229127676883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99467769745962819418451255 149201654618944229127676883)
  ·
    refine ⟨223802481928416343691515325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149201654618944229127676883 223802481928416343691515325)
    ·
      refine ⟨83925930723156128884318247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223802481928416343691515325 83925930723156128884318247)
      ·
        refine ⟨125888896084734193326477371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83925930723156128884318247 125888896084734193326477371)
        ·
          refine ⟨188833344127101289989716057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125888896084734193326477371 188833344127101289989716057)
          ·
            refine ⟨141625008095325967492287043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188833344127101289989716057 141625008095325967492287043)
            ·
              refine ⟨212437512142988951238430565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141625008095325967492287043 212437512142988951238430565)
              ·
                refine ⟨39832033526810428357205731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212437512142988951238430565 39832033526810428357205731)
                ·
                  refine ⟨59748050290215642535808597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39832033526810428357205731 59748050290215642535808597)
                  ·
                    refine ⟨700172464338464560966507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59748050290215642535808597 700172464338464560966507)
                    ·
                      rfl

theorem cell23_4090743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_4090743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090743 prefixEnd_4090743 := by exact prefixLift 4090743
  have htrace : WordTrace (prefixWord ++ tailWord_4090743) baseStart_4090743 baseEnd_4090743 := by
    simpa [prefixWord, tailWord_4090743, baseEnd_4090743] using wordTrace_append hprefix tailTrace_4090743
  have hstable : (prefixWord ++ tailWord_4090743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090743).length < 2 ^ (prefixWord ++ tailWord_4090743).sum := by decide
  have hdescent : baseEnd_4090743 < baseStart_4090743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090778 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3]
def baseStart_4090778 : Nat := 118140960795 + 4090778 * 2 ^ 59
def prefixEnd_4090778 : Nat := 4983230072969 + 3 ^ 40 * 4090778 * 2
def baseEnd_4090778 : Nat := 2100535364838301045961861

theorem tailTrace_4090778 : CollatzResearch.WordTrace tailWord_4090778 prefixEnd_4090778 2100535364838301045961861 := by
  unfold tailWord_4090778
  simp only [CollatzResearch.WordTrace]
  refine ⟨37300732793454357526300247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99468620782544953403467325 37300732793454357526300247)
  ·
    refine ⟨55951099190181536289450371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37300732793454357526300247 55951099190181536289450371)
    ·
      refine ⟨83926648785272304434175557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55951099190181536289450371 83926648785272304434175557)
      ·
        refine ⟨15736246647238557081407917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83926648785272304434175557 15736246647238557081407917)
        ·
          refine ⟨5901092492714458905527969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15736246647238557081407917 5901092492714458905527969)
          ·
            refine ⟨4425819369535844179145977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5901092492714458905527969 4425819369535844179145977)
            ·
              refine ⟨3319364527151883134359483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4425819369535844179145977 3319364527151883134359483)
              ·
                refine ⟨4979046790727824701539225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319364527151883134359483 4979046790727824701539225)
                ·
                  refine ⟨3734285093045868526154419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979046790727824701539225 3734285093045868526154419)
                  ·
                    refine ⟨5601427639568802789231629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3734285093045868526154419 5601427639568802789231629)
                    ·
                      refine ⟨2100535364838301045961861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5601427639568802789231629 2100535364838301045961861)
                      ·
                        rfl

theorem cell23_4090778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_4090778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090778 prefixEnd_4090778 := by exact prefixLift 4090778
  have htrace : WordTrace (prefixWord ++ tailWord_4090778) baseStart_4090778 baseEnd_4090778 := by
    simpa [prefixWord, tailWord_4090778, baseEnd_4090778] using wordTrace_append hprefix tailTrace_4090778
  have hstable : (prefixWord ++ tailWord_4090778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090778).length < 2 ^ (prefixWord ++ tailWord_4090778).sum := by decide
  have hdescent : baseEnd_4090778 < baseStart_4090778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090804 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4090804 : Nat := 118140960795 + 4090804 * 2 ^ 59
def prefixEnd_4090804 : Nat := 4983230072969 + 3 ^ 40 * 4090804 * 2
def baseEnd_4090804 : Nat := 2100548715335317944236741

theorem tailTrace_4090804 : CollatzResearch.WordTrace tailWord_4090804 prefixEnd_4090804 2100548715335317944236741 := by
  unfold tailWord_4090804
  simp only [CollatzResearch.WordTrace]
  refine ⟨74601939735861618272823733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99469252981148824363764977 74601939735861618272823733)
  ·
    refine ⟨6993931850237026713077225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74601939735861618272823733 6993931850237026713077225)
    ·
      refine ⟨5245448887677770034807919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6993931850237026713077225 5245448887677770034807919)
      ·
        refine ⟨7868173331516655052211879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5245448887677770034807919 7868173331516655052211879)
        ·
          refine ⟨11802259997274982578317819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868173331516655052211879 11802259997274982578317819)
          ·
            refine ⟨17703389995912473867476729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11802259997274982578317819 17703389995912473867476729)
            ·
              refine ⟨13277542496934355400607547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17703389995912473867476729 13277542496934355400607547)
              ·
                refine ⟨19916313745401533100911321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13277542496934355400607547 19916313745401533100911321)
                ·
                  refine ⟨14937235309051149825683491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19916313745401533100911321 14937235309051149825683491)
                  ·
                    refine ⟨22405852963576724738525237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14937235309051149825683491 22405852963576724738525237)
                    ·
                      refine ⟨2100548715335317944236741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22405852963576724738525237 2100548715335317944236741)
                      ·
                        rfl

theorem cell23_4090804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4090804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090804 prefixEnd_4090804 := by exact prefixLift 4090804
  have htrace : WordTrace (prefixWord ++ tailWord_4090804) baseStart_4090804 baseEnd_4090804 := by
    simpa [prefixWord, tailWord_4090804, baseEnd_4090804] using wordTrace_append hprefix tailTrace_4090804
  have hstable : (prefixWord ++ tailWord_4090804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090804).length < 2 ^ (prefixWord ++ tailWord_4090804).sum := by decide
  have hdescent : baseEnd_4090804 < baseStart_4090804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090824 : List Nat := [2, 1, 3, 1, 5, 1, 1, 4, 5]
def baseStart_4090824 : Nat := 118140960795 + 4090824 * 2 ^ 59
def prefixEnd_4090824 : Nat := 4983230072969 + 3 ^ 40 * 4090824 * 2
def baseEnd_4090824 : Nat := 233395442772045318442961

theorem tailTrace_4090824 : CollatzResearch.WordTrace tailWord_4090824 prefixEnd_4090824 233395442772045318442961 := by
  unfold tailWord_4090824
  simp only [CollatzResearch.WordTrace]
  refine ⟨74602304465825389980687763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99469739287767186640917017 74602304465825389980687763)
  ·
    refine ⟨111903456698738084971031645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74602304465825389980687763 111903456698738084971031645)
    ·
      refine ⟨41963796262026781864136867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111903456698738084971031645 41963796262026781864136867)
      ·
        refine ⟨62945694393040172796205301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41963796262026781864136867 62945694393040172796205301)
        ·
          refine ⟨5901158849347516199644247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62945694393040172796205301 5901158849347516199644247)
          ·
            refine ⟨8851738274021274299466371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5901158849347516199644247 8851738274021274299466371)
            ·
              refine ⟨13277607411031911449199557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851738274021274299466371 13277607411031911449199557)
              ·
                refine ⟨2489551389568483396724917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13277607411031911449199557 2489551389568483396724917)
                ·
                  refine ⟨233395442772045318442961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2489551389568483396724917 233395442772045318442961)
                  ·
                    rfl

theorem cell23_4090824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 5].length) (baseStart_4090824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090824 prefixEnd_4090824 := by exact prefixLift 4090824
  have htrace : WordTrace (prefixWord ++ tailWord_4090824) baseStart_4090824 baseEnd_4090824 := by
    simpa [prefixWord, tailWord_4090824, baseEnd_4090824] using wordTrace_append hprefix tailTrace_4090824
  have hstable : (prefixWord ++ tailWord_4090824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090824).length < 2 ^ (prefixWord ++ tailWord_4090824).sum := by decide
  have hdescent : baseEnd_4090824 < baseStart_4090824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090827 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 2, 5, 2]
def baseStart_4090827 : Nat := 118140960795 + 4090827 * 2 ^ 59
def prefixEnd_4090827 : Nat := 4983230072969 + 3 ^ 40 * 4090827 * 2
def baseEnd_4090827 : Nat := 2100560525390371354249135

theorem tailTrace_4090827 : CollatzResearch.WordTrace tailWord_4090827 prefixEnd_4090827 2100560525390371354249135 := by
  unfold tailWord_4090827
  simp only [CollatzResearch.WordTrace]
  refine ⟨149204718350639911473734735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99469812233759940982489823 149204718350639911473734735)
  ·
    refine ⟨223807077525959867210602103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149204718350639911473734735 223807077525959867210602103)
    ·
      refine ⟨335710616288939800815903155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223807077525959867210602103 335710616288939800815903155)
      ·
        refine ⟨503565924433409701223854733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335710616288939800815903155 503565924433409701223854733)
        ·
          refine ⟨188837221662528637958945525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503565924433409701223854733 188837221662528637958945525)
          ·
            refine ⟨17703489530862059808651143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188837221662528637958945525 17703489530862059808651143)
            ·
              refine ⟨26555234296293089712976715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17703489530862059808651143 26555234296293089712976715)
              ·
                refine ⟨39832851444439634569465073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26555234296293089712976715 39832851444439634569465073)
                ·
                  refine ⟨29874638583329725927098805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39832851444439634569465073 29874638583329725927098805)
                  ·
                    refine ⟨2800747367187161805665513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29874638583329725927098805 2800747367187161805665513)
                    ·
                      refine ⟨2100560525390371354249135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800747367187161805665513 2100560525390371354249135)
                      ·
                        rfl

theorem cell23_4090827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 5, 2].length) (baseStart_4090827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090827 prefixEnd_4090827 := by exact prefixLift 4090827
  have htrace : WordTrace (prefixWord ++ tailWord_4090827) baseStart_4090827 baseEnd_4090827 := by
    simpa [prefixWord, tailWord_4090827, baseEnd_4090827] using wordTrace_append hprefix tailTrace_4090827
  have hstable : (prefixWord ++ tailWord_4090827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090827).length < 2 ^ (prefixWord ++ tailWord_4090827).sum := by decide
  have hdescent : baseEnd_4090827 < baseStart_4090827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090834 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_4090834 : Nat := 118140960795 + 4090834 * 2 ^ 59
def prefixEnd_4090834 : Nat := 4983230072969 + 3 ^ 40 * 4090834 * 2
def baseEnd_4090834 : Nat := 2100564119754952826861603

theorem tailTrace_4090834 : CollatzResearch.WordTrace tailWord_4090834 prefixEnd_4090834 2100564119754952826861603 := by
  unfold tailWord_4090834
  simp only [CollatzResearch.WordTrace]
  refine ⟨37301243415403637917309889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99469982441076367779493037 37301243415403637917309889)
  ·
    refine ⟨27975932561552728437982417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37301243415403637917309889 27975932561552728437982417)
    ·
      refine ⟨20981949421164546328486813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27975932561552728437982417 20981949421164546328486813)
      ·
        refine ⟨7868231032936704873182555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20981949421164546328486813 7868231032936704873182555)
        ·
          refine ⟨11802346549405057309773833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868231032936704873182555 11802346549405057309773833)
          ·
            refine ⟨8851759912053792982330375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11802346549405057309773833 8851759912053792982330375)
            ·
              refine ⟨13277639868080689473495563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851759912053792982330375 13277639868080689473495563)
              ·
                refine ⟨19916459802121034210243345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13277639868080689473495563 19916459802121034210243345)
                ·
                  refine ⟨14937344851590775657682509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19916459802121034210243345 14937344851590775657682509)
                  ·
                    refine ⟨5601504319346540871630941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14937344851590775657682509 5601504319346540871630941)
                    ·
                      refine ⟨2100564119754952826861603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5601504319346540871630941 2100564119754952826861603)
                      ·
                        rfl

theorem cell23_4090834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_4090834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090834 prefixEnd_4090834 := by exact prefixLift 4090834
  have htrace : WordTrace (prefixWord ++ tailWord_4090834) baseStart_4090834 baseEnd_4090834 := by
    simpa [prefixWord, tailWord_4090834, baseEnd_4090834] using wordTrace_append hprefix tailTrace_4090834
  have hstable : (prefixWord ++ tailWord_4090834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090834).length < 2 ^ (prefixWord ++ tailWord_4090834).sum := by decide
  have hdescent : baseEnd_4090834 < baseStart_4090834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090877 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_4090877 : Nat := 118140960795 + 4090877 * 2 ^ 59
def prefixEnd_4090877 : Nat := 4983230072969 + 3 ^ 40 * 4090877 * 2
def baseEnd_4090877 : Nat := 2100586199423096158623905

theorem tailTrace_4090877 : CollatzResearch.WordTrace tailWord_4090877 prefixEnd_4090877 2100586199423096158623905 := by
  unfold tailWord_4090877
  simp only [CollatzResearch.WordTrace]
  refine ⟨149206542000458770013054885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99471028000305846675369923 149206542000458770013054885)
  ·
    refine ⟨27976226625086019377447791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149206542000458770013054885 27976226625086019377447791)
    ·
      refine ⟨41964339937629029066171687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27976226625086019377447791 41964339937629029066171687)
      ·
        refine ⟨62946509906443543599257531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41964339937629029066171687 62946509906443543599257531)
        ·
          refine ⟨94419764859665315398886297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62946509906443543599257531 94419764859665315398886297)
          ·
            refine ⟨70814823644748986549164723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94419764859665315398886297 70814823644748986549164723)
            ·
              refine ⟨106222235467123479823747085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70814823644748986549164723 106222235467123479823747085)
              ·
                refine ⟨39833338300171304933905157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106222235467123479823747085 39833338300171304933905157)
                ·
                  refine ⟨7468750931282119675107217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39833338300171304933905157 7468750931282119675107217)
                  ·
                    refine ⟨5601563198461589756330413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7468750931282119675107217 5601563198461589756330413)
                    ·
                      refine ⟨2100586199423096158623905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5601563198461589756330413 2100586199423096158623905)
                      ·
                        rfl

theorem cell23_4090877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_4090877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090877 prefixEnd_4090877 := by exact prefixLift 4090877
  have htrace : WordTrace (prefixWord ++ tailWord_4090877) baseStart_4090877 baseEnd_4090877 := by
    simpa [prefixWord, tailWord_4090877, baseEnd_4090877] using wordTrace_append hprefix tailTrace_4090877
  have hstable : (prefixWord ++ tailWord_4090877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090877).length < 2 ^ (prefixWord ++ tailWord_4090877).sum := by decide
  have hdescent : baseEnd_4090877 < baseStart_4090877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090941 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_4090941 : Nat := 118140960795 + 4090941 * 2 ^ 59
def prefixEnd_4090941 : Nat := 4983230072969 + 3 ^ 40 * 4090941 * 2
def baseEnd_4090941 : Nat := 2100619062184983908223611

theorem tailTrace_4090941 : CollatzResearch.WordTrace tailWord_4090941 prefixEnd_4090941 2100619062184983908223611 := by
  unfold tailWord_4090941
  simp only [CollatzResearch.WordTrace]
  refine ⟨149208876272226908943384677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99472584181484605962256451 149208876272226908943384677)
  ·
    refine ⟨27976664301042545426884627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149208876272226908943384677 27976664301042545426884627)
    ·
      refine ⟨41964996451563818140326941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27976664301042545426884627 41964996451563818140326941)
      ·
        refine ⟨15736873669336431802622603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41964996451563818140326941 15736873669336431802622603)
        ·
          refine ⟨23605310504004647703933905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15736873669336431802622603 23605310504004647703933905)
          ·
            refine ⟨17703982878003485777950429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23605310504004647703933905 17703982878003485777950429)
            ·
              refine ⟨6638993579251307166731411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17703982878003485777950429 6638993579251307166731411)
              ·
                refine ⟨9958490368876960750097117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6638993579251307166731411 9958490368876960750097117)
                ·
                  refine ⟨3734433888328860281286419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9958490368876960750097117 3734433888328860281286419)
                  ·
                    refine ⟨5601650832493290421929629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3734433888328860281286419 5601650832493290421929629)
                    ·
                      refine ⟨2100619062184983908223611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5601650832493290421929629 2100619062184983908223611)
                      ·
                        rfl

theorem cell23_4090941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_4090941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090941 prefixEnd_4090941 := by exact prefixLift 4090941
  have htrace : WordTrace (prefixWord ++ tailWord_4090941) baseStart_4090941 baseEnd_4090941 := by
    simpa [prefixWord, tailWord_4090941, baseEnd_4090941] using wordTrace_append hprefix tailTrace_4090941
  have hstable : (prefixWord ++ tailWord_4090941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090941).length < 2 ^ (prefixWord ++ tailWord_4090941).sum := by decide
  have hdescent : baseEnd_4090941 < baseStart_4090941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090947 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 4]
def baseStart_4090947 : Nat := 118140960795 + 4090947 * 2 ^ 59
def prefixEnd_4090947 : Nat := 4983230072969 + 3 ^ 40 * 4090947 * 2
def baseEnd_4090947 : Nat := 2100622143068910884748583

theorem tailTrace_4090947 : CollatzResearch.WordTrace tailWord_4090947 prefixEnd_4090947 2100622143068910884748583 := by
  unfold tailWord_4090947
  simp only [CollatzResearch.WordTrace]
  refine ⟨149209095110205171968103095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99472730073470114645402063 149209095110205171968103095)
  ·
    refine ⟨223813642665307757952154643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149209095110205171968103095 223813642665307757952154643)
    ·
      refine ⟨335720463997961636928231965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223813642665307757952154643 335720463997961636928231965)
      ·
        refine ⟨125895173999235613848086987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335720463997961636928231965 125895173999235613848086987)
        ·
          refine ⟨188842760998853420772130481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125895173999235613848086987 188842760998853420772130481)
          ·
            refine ⟨141632070749140065579097861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188842760998853420772130481 141632070749140065579097861)
            ·
              refine ⟨26556013265463762296080849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141632070749140065579097861 26556013265463762296080849)
              ·
                refine ⟨19917009949097821722060637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26556013265463762296080849 19917009949097821722060637)
                ·
                  refine ⟨7468878730911683145772739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19917009949097821722060637 7468878730911683145772739)
                  ·
                    refine ⟨11203318096367524718659109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7468878730911683145772739 11203318096367524718659109)
                    ·
                      refine ⟨2100622143068910884748583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11203318096367524718659109 2100622143068910884748583)
                      ·
                        rfl

theorem cell23_4090947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_4090947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090947 prefixEnd_4090947 := by exact prefixLift 4090947
  have htrace : WordTrace (prefixWord ++ tailWord_4090947) baseStart_4090947 baseEnd_4090947 := by
    simpa [prefixWord, tailWord_4090947, baseEnd_4090947] using wordTrace_append hprefix tailTrace_4090947
  have hstable : (prefixWord ++ tailWord_4090947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090947).length < 2 ^ (prefixWord ++ tailWord_4090947).sum := by decide
  have hdescent : baseEnd_4090947 < baseStart_4090947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090964 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_4090964 : Nat := 118140960795 + 4090964 * 2 ^ 59
def prefixEnd_4090964 : Nat := 4983230072969 + 3 ^ 40 * 4090964 * 2
def baseEnd_4090964 : Nat := 2100630872240037318236005

theorem tailTrace_4090964 : CollatzResearch.WordTrace tailWord_4090964 prefixEnd_4090964 2100630872240037318236005 := by
  unfold tailWord_4090964
  simp only [CollatzResearch.WordTrace]
  refine ⟨74604857575571791935735973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99473143434095722580981297 74604857575571791935735973)
  ·
    refine ⟨13988410795419710987950495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74604857575571791935735973 13988410795419710987950495)
    ·
      refine ⟨20982616193129566481925743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13988410795419710987950495 20982616193129566481925743)
      ·
        refine ⟨31473924289694349722888615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20982616193129566481925743 31473924289694349722888615)
        ·
          refine ⟨47210886434541524584332923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31473924289694349722888615 47210886434541524584332923)
          ·
            refine ⟨70816329651812286876499385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47210886434541524584332923 70816329651812286876499385)
            ·
              refine ⟨53112247238859215157374539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70816329651812286876499385 53112247238859215157374539)
              ·
                refine ⟨79668370858288822736061809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53112247238859215157374539 79668370858288822736061809)
                ·
                  refine ⟨59751278143716617052046357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79668370858288822736061809 59751278143716617052046357)
                  ·
                    refine ⟨2800841162986716424314673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59751278143716617052046357 2800841162986716424314673)
                    ·
                      refine ⟨2100630872240037318236005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800841162986716424314673 2100630872240037318236005)
                      ·
                        rfl

theorem cell23_4090964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_4090964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090964 prefixEnd_4090964 := by exact prefixLift 4090964
  have htrace : WordTrace (prefixWord ++ tailWord_4090964) baseStart_4090964 baseEnd_4090964 := by
    simpa [prefixWord, tailWord_4090964, baseEnd_4090964] using wordTrace_append hprefix tailTrace_4090964
  have hstable : (prefixWord ++ tailWord_4090964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090964).length < 2 ^ (prefixWord ++ tailWord_4090964).sum := by decide
  have hdescent : baseEnd_4090964 < baseStart_4090964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090977 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_4090977 : Nat := 118140960795 + 4090977 * 2 ^ 59
def prefixEnd_4090977 : Nat := 4983230072969 + 3 ^ 40 * 4090977 * 2
def baseEnd_4090977 : Nat := 2100637547488545767373445

theorem tailTrace_4090977 : CollatzResearch.WordTrace tailWord_4090977 prefixEnd_4090977 2100637547488545767373445 := by
  unfold tailWord_4090977
  simp only [CollatzResearch.WordTrace]
  refine ⟨149210189300096487091695185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99473459533397658061130123 149210189300096487091695185)
  ·
    refine ⟨111907641975072365318771389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149210189300096487091695185 111907641975072365318771389)
    ·
      refine ⟨41965365740652136994539271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111907641975072365318771389 41965365740652136994539271)
      ·
        refine ⟨62948048610978205491808907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41965365740652136994539271 62948048610978205491808907)
        ·
          refine ⟨94422072916467308237713361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62948048610978205491808907 94422072916467308237713361)
          ·
            refine ⟨70816554687350481178285021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94422072916467308237713361 70816554687350481178285021)
            ·
              refine ⟨26556208007756430441856883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70816554687350481178285021 26556208007756430441856883)
              ·
                refine ⟨39834312011634645662785325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26556208007756430441856883 39834312011634645662785325)
                ·
                  refine ⟨14937867004362992123544497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39834312011634645662785325 14937867004362992123544497)
                  ·
                    refine ⟨11203400253272244092658373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14937867004362992123544497 11203400253272244092658373)
                    ·
                      refine ⟨2100637547488545767373445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11203400253272244092658373 2100637547488545767373445)
                      ·
                        rfl

theorem cell23_4090977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_4090977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090977 prefixEnd_4090977 := by exact prefixLift 4090977
  have htrace : WordTrace (prefixWord ++ tailWord_4090977) baseStart_4090977 baseEnd_4090977 := by
    simpa [prefixWord, tailWord_4090977, baseEnd_4090977] using wordTrace_append hprefix tailTrace_4090977
  have hstable : (prefixWord ++ tailWord_4090977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090977).length < 2 ^ (prefixWord ++ tailWord_4090977).sum := by decide
  have hdescent : baseEnd_4090977 < baseStart_4090977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090978 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4090978 : Nat := 118140960795 + 4090978 * 2 ^ 59
def prefixEnd_4090978 : Nat := 4983230072969 + 3 ^ 40 * 4090978 * 2
def baseEnd_4090978 : Nat := 700212686989733421153647

theorem tailTrace_4090978 : CollatzResearch.WordTrace tailWord_4090978 prefixEnd_4090978 700212686989733421153647 := by
  unfold tailWord_4090978
  simp only [CollatzResearch.WordTrace]
  refine ⟨37302556443273216065620397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99473483848728576174987725 37302556443273216065620397)
  ·
    refine ⟨13988458666227456024607649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37302556443273216065620397 13988458666227456024607649)
    ·
      refine ⟨10491343999670592018455737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13988458666227456024607649 10491343999670592018455737)
      ·
        refine ⟨7868507999752944013841803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10491343999670592018455737 7868507999752944013841803)
        ·
          refine ⟨11802761999629416020762705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868507999752944013841803 11802761999629416020762705)
          ·
            refine ⟨8852071499722062015572029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11802761999629416020762705 8852071499722062015572029)
            ·
              refine ⟨3319526812395773255839511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8852071499722062015572029 3319526812395773255839511)
              ·
                refine ⟨4979290218593659883759267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319526812395773255839511 4979290218593659883759267)
                ·
                  refine ⟨7468935327890489825638901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979290218593659883759267 7468935327890489825638901)
                  ·
                    refine ⟨700212686989733421153647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7468935327890489825638901 700212686989733421153647)
                    ·
                      rfl

theorem cell23_4090978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4090978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090978 prefixEnd_4090978 := by exact prefixLift 4090978
  have htrace : WordTrace (prefixWord ++ tailWord_4090978) baseStart_4090978 baseEnd_4090978 := by
    simpa [prefixWord, tailWord_4090978, baseEnd_4090978] using wordTrace_append hprefix tailTrace_4090978
  have hstable : (prefixWord ++ tailWord_4090978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090978).length < 2 ^ (prefixWord ++ tailWord_4090978).sum := by decide
  have hdescent : baseEnd_4090978 < baseStart_4090978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090981 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 1, 1, 4]
def baseStart_4090981 : Nat := 118140960795 + 4090981 * 2 ^ 59
def prefixEnd_4090981 : Nat := 4983230072969 + 3 ^ 40 * 4090981 * 2
def baseEnd_4090981 : Nat := 2100639601411163751723427

theorem tailTrace_4090981 : CollatzResearch.WordTrace tailWord_4090981 prefixEnd_4090981 2100639601411163751723427 := by
  unfold tailWord_4090981
  simp only [CollatzResearch.WordTrace]
  refine ⟨149210335192081995774840797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99473556794721330516560531 149210335192081995774840797)
  ·
    refine ⟨55953875697030748415565299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149210335192081995774840797 55953875697030748415565299)
    ·
      refine ⟨83930813545546122623347949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55953875697030748415565299 83930813545546122623347949)
      ·
        refine ⟨31474055079579795983755481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83930813545546122623347949 31474055079579795983755481)
        ·
          refine ⟨23605541309684846987816611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31474055079579795983755481 23605541309684846987816611)
          ·
            refine ⟨35408311964527270481724917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23605541309684846987816611 35408311964527270481724917)
            ·
              refine ⟨3319529246674431607661711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35408311964527270481724917 3319529246674431607661711)
              ·
                refine ⟨4979293870011647411492567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319529246674431607661711 4979293870011647411492567)
                ·
                  refine ⟨7468940805017471117238851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979293870011647411492567 7468940805017471117238851)
                  ·
                    refine ⟨11203411207526206675858277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7468940805017471117238851 11203411207526206675858277)
                    ·
                      refine ⟨2100639601411163751723427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11203411207526206675858277 2100639601411163751723427)
                      ·
                        rfl

theorem cell23_4090981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_4090981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090981 prefixEnd_4090981 := by exact prefixLift 4090981
  have htrace : WordTrace (prefixWord ++ tailWord_4090981) baseStart_4090981 baseEnd_4090981 := by
    simpa [prefixWord, tailWord_4090981, baseEnd_4090981] using wordTrace_append hprefix tailTrace_4090981
  have hstable : (prefixWord ++ tailWord_4090981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090981).length < 2 ^ (prefixWord ++ tailWord_4090981).sum := by decide
  have hdescent : baseEnd_4090981 < baseStart_4090981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4090998 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_4090998 : Nat := 118140960795 + 4090998 * 2 ^ 59
def prefixEnd_4090998 : Nat := 4983230072969 + 3 ^ 40 * 4090998 * 2
def baseEnd_4090998 : Nat := 2100648330582290185210849

theorem tailTrace_4090998 : CollatzResearch.WordTrace tailWord_4090998 prefixEnd_4090998 2100648330582290185210849 := by
  unfold tailWord_4090998
  simp only [CollatzResearch.WordTrace]
  refine ⟨9325684702063775479888103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99473970155346938452139765 9325684702063775479888103)
  ·
    refine ⟨13988527053095663219832155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9325684702063775479888103 13988527053095663219832155)
    ·
      refine ⟨20982790579643494829748233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13988527053095663219832155 20982790579643494829748233)
      ·
        refine ⟨15737092934732621122311175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20982790579643494829748233 15737092934732621122311175)
        ·
          refine ⟨23605639402098931683466763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15737092934732621122311175 23605639402098931683466763)
          ·
            refine ⟨35408459103148397525200145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23605639402098931683466763 35408459103148397525200145)
            ·
              refine ⟨26556344327361298143900109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35408459103148397525200145 26556344327361298143900109)
              ·
                refine ⟨9958629122760486803962541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26556344327361298143900109 9958629122760486803962541)
                ·
                  refine ⟨3734485921035182551485953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9958629122760486803962541 3734485921035182551485953)
                  ·
                    refine ⟨2800864440776386913614465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3734485921035182551485953 2800864440776386913614465)
                    ·
                      refine ⟨2100648330582290185210849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800864440776386913614465 2100648330582290185210849)
                      ·
                        rfl

theorem cell23_4090998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_4090998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4090998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4090998 prefixEnd_4090998 := by exact prefixLift 4090998
  have htrace : WordTrace (prefixWord ++ tailWord_4090998) baseStart_4090998 baseEnd_4090998 := by
    simpa [prefixWord, tailWord_4090998, baseEnd_4090998] using wordTrace_append hprefix tailTrace_4090998
  have hstable : (prefixWord ++ tailWord_4090998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4090998).length < 2 ^ (prefixWord ++ tailWord_4090998).sum := by decide
  have hdescent : baseEnd_4090998 < baseStart_4090998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4090998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091062 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4091062 : Nat := 118140960795 + 4091062 * 2 ^ 59
def prefixEnd_4091062 : Nat := 4983230072969 + 3 ^ 40 * 4091062 * 2
def baseEnd_4091062 : Nat := 2100681193344177934810555

theorem tailTrace_4091062 : CollatzResearch.WordTrace tailWord_4091062 prefixEnd_4091062 2100681193344177934810555 := by
  unfold tailWord_4091062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9325830594049284163033715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99475526336525697739026293 9325830594049284163033715)
  ·
    refine ⟨13988745891073926244550573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9325830594049284163033715 13988745891073926244550573)
    ·
      refine ⟨5245779709152722341706465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13988745891073926244550573 5245779709152722341706465)
      ·
        refine ⟨3934334781864541756279849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5245779709152722341706465 3934334781864541756279849)
        ·
          refine ⟨2950751086398406317209887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3934334781864541756279849 2950751086398406317209887)
          ·
            refine ⟨4426126629597609475814831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950751086398406317209887 4426126629597609475814831)
            ·
              refine ⟨6639189944396414213722247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426126629597609475814831 6639189944396414213722247)
              ·
                refine ⟨9958784916594621320583371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6639189944396414213722247 9958784916594621320583371)
                ·
                  refine ⟨14938177374891931980875057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9958784916594621320583371 14938177374891931980875057)
                  ·
                    refine ⟨11203633031168948985656293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14938177374891931980875057 11203633031168948985656293)
                    ·
                      refine ⟨2100681193344177934810555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11203633031168948985656293 2100681193344177934810555)
                      ·
                        rfl

theorem cell23_4091062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4091062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091062 prefixEnd_4091062 := by exact prefixLift 4091062
  have htrace : WordTrace (prefixWord ++ tailWord_4091062) baseStart_4091062 baseEnd_4091062 := by
    simpa [prefixWord, tailWord_4091062, baseEnd_4091062] using wordTrace_append hprefix tailTrace_4091062
  have hstable : (prefixWord ++ tailWord_4091062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091062).length < 2 ^ (prefixWord ++ tailWord_4091062).sum := by decide
  have hdescent : baseEnd_4091062 < baseStart_4091062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091067 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 4]
def baseStart_4091067 : Nat := 118140960795 + 4091067 * 2 ^ 59
def prefixEnd_4091067 : Nat := 4983230072969 + 3 ^ 40 * 4091067 * 2
def baseEnd_4091067 : Nat := 2100683760747450415248031

theorem tailTrace_4091067 : CollatzResearch.WordTrace tailWord_4091067 prefixEnd_4091067 2100683760747450415248031 := by
  unfold tailWord_4091067
  simp only [CollatzResearch.WordTrace]
  refine ⟨149213471869770432462471455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99475647913180288308314303 149213471869770432462471455)
  ·
    refine ⟨223820207804655648693707183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149213471869770432462471455 223820207804655648693707183)
    ·
      refine ⟨335730311706983473040560775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223820207804655648693707183 335730311706983473040560775)
      ·
        refine ⟨503595467560475209560841163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335730311706983473040560775 503595467560475209560841163)
        ·
          refine ⟨755393201340712814341261745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503595467560475209560841163 755393201340712814341261745)
          ·
            refine ⟨566544901005534610755946309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755393201340712814341261745 566544901005534610755946309)
            ·
              refine ⟨106227168938537739516739933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 566544901005534610755946309 106227168938537739516739933)
              ·
                refine ⟨39835188351951652318777475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106227168938537739516739933 39835188351951652318777475)
                ·
                  refine ⟨59752782527927478478166213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39835188351951652318777475 59752782527927478478166213)
                  ·
                    refine ⟨11203646723986402214656165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59752782527927478478166213 11203646723986402214656165)
                    ·
                      refine ⟨2100683760747450415248031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11203646723986402214656165 2100683760747450415248031)
                      ·
                        rfl

theorem cell23_4091067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 4].length) (baseStart_4091067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091067 prefixEnd_4091067 := by exact prefixLift 4091067
  have htrace : WordTrace (prefixWord ++ tailWord_4091067) baseStart_4091067 baseEnd_4091067 := by
    simpa [prefixWord, tailWord_4091067, baseEnd_4091067] using wordTrace_append hprefix tailTrace_4091067
  have hstable : (prefixWord ++ tailWord_4091067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091067).length < 2 ^ (prefixWord ++ tailWord_4091067).sum := by decide
  have hdescent : baseEnd_4091067 < baseStart_4091067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091071 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 1, 4, 2]
def baseStart_4091071 : Nat := 118140960795 + 4091071 * 2 ^ 59
def prefixEnd_4091071 : Nat := 4983230072969 + 3 ^ 40 * 4091071 * 2
def baseEnd_4091071 : Nat := 2100685814670068399598013

theorem tailTrace_4091071 : CollatzResearch.WordTrace tailWord_4091071 prefixEnd_4091071 2100685814670068399598013 := by
  unfold tailWord_4091071
  simp only [CollatzResearch.WordTrace]
  refine ⟨149213617761755941145617067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99475745174503960763744711 149213617761755941145617067)
  ·
    refine ⟨223820426642633911718425601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149213617761755941145617067 223820426642633911718425601)
    ·
      refine ⟨167865319981975433788819201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223820426642633911718425601 167865319981975433788819201)
      ·
        refine ⟨125898989986481575341614401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167865319981975433788819201 125898989986481575341614401)
        ·
          refine ⟨94424242489861181506210801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125898989986481575341614401 94424242489861181506210801)
          ·
            refine ⟨70818181867395886129658101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94424242489861181506210801 70818181867395886129658101)
            ·
              refine ⟨6639204550068364324655447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70818181867395886129658101 6639204550068364324655447)
              ·
                refine ⟨9958806825102546486983171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6639204550068364324655447 9958806825102546486983171)
                ·
                  refine ⟨14938210237653819730474757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9958806825102546486983171 14938210237653819730474757)
                  ·
                    refine ⟨2800914419560091199464017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14938210237653819730474757 2800914419560091199464017)
                    ·
                      refine ⟨2100685814670068399598013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800914419560091199464017 2100685814670068399598013)
                      ·
                        rfl

theorem cell23_4091071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 4, 2].length) (baseStart_4091071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091071 prefixEnd_4091071 := by exact prefixLift 4091071
  have htrace : WordTrace (prefixWord ++ tailWord_4091071) baseStart_4091071 baseEnd_4091071 := by
    simpa [prefixWord, tailWord_4091071, baseEnd_4091071] using wordTrace_append hprefix tailTrace_4091071
  have hstable : (prefixWord ++ tailWord_4091071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091071).length < 2 ^ (prefixWord ++ tailWord_4091071).sum := by decide
  have hdescent : baseEnd_4091071 < baseStart_4091071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091178 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_4091178 : Nat := 118140960795 + 4091178 * 2 ^ 59
def prefixEnd_4091178 : Nat := 4983230072969 + 3 ^ 40 * 4091178 * 2
def baseEnd_4091178 : Nat := 2100740757100099480960021

theorem tailTrace_4091178 : CollatzResearch.WordTrace tailWord_4091178 prefixEnd_4091178 2100740757100099480960021 := by
  unfold tailWord_4091178
  simp only [CollatzResearch.WordTrace]
  refine ⟨37304380093092074604940547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99478346914912198946508125 37304380093092074604940547)
  ·
    refine ⟨55956570139638111907410821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37304380093092074604940547 55956570139638111907410821)
    ·
      refine ⟨10491856901182145982639529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55956570139638111907410821 10491856901182145982639529)
      ·
        refine ⟨7868892675886609486979647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10491856901182145982639529 7868892675886609486979647)
        ·
          refine ⟨11803339013829914230469471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868892675886609486979647 11803339013829914230469471)
          ·
            refine ⟨17705008520744871345704207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11803339013829914230469471 17705008520744871345704207)
            ·
              refine ⟨26557512781117307018556311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17705008520744871345704207 26557512781117307018556311)
              ·
                refine ⟨39836269171675960527834467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26557512781117307018556311 39836269171675960527834467)
                ·
                  refine ⟨59754403757513940791751701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39836269171675960527834467 59754403757513940791751701)
                  ·
                    refine ⟨2800987676133465974613361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59754403757513940791751701 2800987676133465974613361)
                    ·
                      refine ⟨2100740757100099480960021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2800987676133465974613361 2100740757100099480960021)
                      ·
                        rfl

theorem cell23_4091178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_4091178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091178 prefixEnd_4091178 := by exact prefixLift 4091178
  have htrace : WordTrace (prefixWord ++ tailWord_4091178) baseStart_4091178 baseEnd_4091178 := by
    simpa [prefixWord, tailWord_4091178, baseEnd_4091178] using wordTrace_append hprefix tailTrace_4091178
  have hstable : (prefixWord ++ tailWord_4091178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091178).length < 2 ^ (prefixWord ++ tailWord_4091178).sum := by decide
  have hdescent : baseEnd_4091178 < baseStart_4091178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091184 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 6]
def baseStart_4091184 : Nat := 118140960795 + 4091184 * 2 ^ 59
def prefixEnd_4091184 : Nat := 4983230072969 + 3 ^ 40 * 4091184 * 2
def baseEnd_4091184 : Nat := 233415981998225161942777

theorem tailTrace_4091184 : CollatzResearch.WordTrace tailWord_4091184 prefixEnd_4091184 233415981998225161942777 := by
  unfold tailWord_4091184
  simp only [CollatzResearch.WordTrace]
  refine ⟨74608869605173280722240303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99478492806897707629653737 74608869605173280722240303)
  ·
    refine ⟨111913304407759921083360455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74608869605173280722240303 111913304407759921083360455)
    ·
      refine ⟨167869956611639881625040683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111913304407759921083360455 167869956611639881625040683)
      ·
        refine ⟨251804934917459822437561025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167869956611639881625040683 251804934917459822437561025)
        ·
          refine ⟨188853701188094866828170769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251804934917459822437561025 188853701188094866828170769)
          ·
            refine ⟨141640275891071150121128077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188853701188094866828170769 141640275891071150121128077)
            ·
              refine ⟨53115103459151681295423029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141640275891071150121128077 53115103459151681295423029)
              ·
                refine ⟨4979540949295470121445909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53115103459151681295423029 4979540949295470121445909)
                ·
                  refine ⟨233415981998225161942777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4979540949295470121445909 233415981998225161942777)
                  ·
                    rfl

theorem cell23_4091184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 6].length) (baseStart_4091184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091184 prefixEnd_4091184 := by exact prefixLift 4091184
  have htrace : WordTrace (prefixWord ++ tailWord_4091184) baseStart_4091184 baseEnd_4091184 := by
    simpa [prefixWord, tailWord_4091184, baseEnd_4091184] using wordTrace_append hprefix tailTrace_4091184
  have hstable : (prefixWord ++ tailWord_4091184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091184).length < 2 ^ (prefixWord ++ tailWord_4091184).sum := by decide
  have hdescent : baseEnd_4091184 < baseStart_4091184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091188 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_4091188 : Nat := 118140960795 + 4091188 * 2 ^ 59
def prefixEnd_4091188 : Nat := 4983230072969 + 3 ^ 40 * 4091188 * 2
def baseEnd_4091188 : Nat := 700248630635548147278325

theorem tailTrace_4091188 : CollatzResearch.WordTrace tailWord_4091188 prefixEnd_4091188 700248630635548147278325 := by
  unfold tailWord_4091188
  simp only [CollatzResearch.WordTrace]
  refine ⟨74608942551166035063813109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99478590068221380085084145 74608942551166035063813109)
  ·
    refine ⟨6994588364171815787232479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74608942551166035063813109 6994588364171815787232479)
    ·
      refine ⟨10491882546257723680848719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6994588364171815787232479 10491882546257723680848719)
      ·
        refine ⟨15737823819386585521273079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10491882546257723680848719 15737823819386585521273079)
        ·
          refine ⟨23606735729079878281909619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15737823819386585521273079 23606735729079878281909619)
          ·
            refine ⟨35410103593619817422864429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23606735729079878281909619 35410103593619817422864429)
            ·
              refine ⟨13278788847607431533574161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35410103593619817422864429 13278788847607431533574161)
              ·
                refine ⟨9959091635705573650180621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13278788847607431533574161 9959091635705573650180621)
                ·
                  refine ⟨3734659363389590118817733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9959091635705573650180621 3734659363389590118817733)
                  ·
                    refine ⟨700248630635548147278325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3734659363389590118817733 700248630635548147278325)
                    ·
                      rfl

theorem cell23_4091188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_4091188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091188 prefixEnd_4091188 := by exact prefixLift 4091188
  have htrace : WordTrace (prefixWord ++ tailWord_4091188) baseStart_4091188 baseEnd_4091188 := by
    simpa [prefixWord, tailWord_4091188, baseEnd_4091188] using wordTrace_append hprefix tailTrace_4091188
  have hstable : (prefixWord ++ tailWord_4091188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091188).length < 2 ^ (prefixWord ++ tailWord_4091188).sum := by decide
  have hdescent : baseEnd_4091188 < baseStart_4091188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091261 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_4091261 : Nat := 118140960795 + 4091261 * 2 ^ 59
def prefixEnd_4091261 : Nat := 4983230072969 + 3 ^ 40 * 4091261 * 2
def baseEnd_4091261 : Nat := 700261125331474218740713

theorem tailTrace_4091261 : CollatzResearch.WordTrace tailWord_4091261 prefixEnd_4091261 700261125331474218740713 := by
  unfold tailWord_4091261
  simp only [CollatzResearch.WordTrace]
  refine ⟨149220547631067603595033637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99480365087378402396689091 149220547631067603595033637)
  ·
    refine ⟨27978852680825175674068807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149220547631067603595033637 27978852680825175674068807)
    ·
      refine ⟨41968279021237763511103211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27978852680825175674068807 41968279021237763511103211)
      ·
        refine ⟨62952418531856645266654817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41968279021237763511103211 62952418531856645266654817)
        ·
          refine ⟨47214313898892483949991113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62952418531856645266654817 47214313898892483949991113)
          ·
            refine ⟨35410735424169362962493335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47214313898892483949991113 35410735424169362962493335)
            ·
              refine ⟨53116103136254044443740003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35410735424169362962493335 53116103136254044443740003)
              ·
                refine ⟨79674154704381066665610005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53116103136254044443740003 79674154704381066665610005)
                ·
                  refine ⟨3734726001767862499950469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79674154704381066665610005 3734726001767862499950469)
                  ·
                    refine ⟨700261125331474218740713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3734726001767862499950469 700261125331474218740713)
                    ·
                      rfl

theorem cell23_4091261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_4091261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091261 prefixEnd_4091261 := by exact prefixLift 4091261
  have htrace : WordTrace (prefixWord ++ tailWord_4091261) baseStart_4091261 baseEnd_4091261 := by
    simpa [prefixWord, tailWord_4091261, baseEnd_4091261] using wordTrace_append hprefix tailTrace_4091261
  have hstable : (prefixWord ++ tailWord_4091261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091261).length < 2 ^ (prefixWord ++ tailWord_4091261).sum := by decide
  have hdescent : baseEnd_4091261 < baseStart_4091261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091268 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_4091268 : Nat := 118140960795 + 4091268 * 2 ^ 59
def prefixEnd_4091268 : Nat := 4983230072969 + 3 ^ 40 * 4091268 * 2
def baseEnd_4091268 : Nat := 2100786970359004128834607

theorem tailTrace_4091268 : CollatzResearch.WordTrace tailWord_4091268 prefixEnd_4091268 2100786970359004128834607 := by
  unfold tailWord_4091268
  simp only [CollatzResearch.WordTrace]
  refine ⟨74610401471021121895269229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99480535294694829193692305 74610401471021121895269229)
  ·
    refine ⟨27978900551632920710725961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74610401471021121895269229 27978900551632920710725961)
    ·
      refine ⟨20984175413724690533044471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27978900551632920710725961 20984175413724690533044471)
      ·
        refine ⟨31476263120587035799566707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20984175413724690533044471 31476263120587035799566707)
        ·
          refine ⟨47214394680880553699350061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31476263120587035799566707 47214394680880553699350061)
          ·
            refine ⟨17705398005330207637256273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47214394680880553699350061 17705398005330207637256273)
            ·
              refine ⟨13279048503997655727942205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17705398005330207637256273 13279048503997655727942205)
              ·
                refine ⟨4979643188999120897978327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13279048503997655727942205 4979643188999120897978327)
                ·
                  refine ⟨7469464783498681346967491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979643188999120897978327 7469464783498681346967491)
                  ·
                    refine ⟨11204197175248022020451237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7469464783498681346967491 11204197175248022020451237)
                    ·
                      refine ⟨2100786970359004128834607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11204197175248022020451237 2100786970359004128834607)
                      ·
                        rfl

theorem cell23_4091268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_4091268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091268 prefixEnd_4091268 := by exact prefixLift 4091268
  have htrace : WordTrace (prefixWord ++ tailWord_4091268) baseStart_4091268 baseEnd_4091268 := by
    simpa [prefixWord, tailWord_4091268, baseEnd_4091268] using wordTrace_append hprefix tailTrace_4091268
  have hstable : (prefixWord ++ tailWord_4091268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091268).length < 2 ^ (prefixWord ++ tailWord_4091268).sum := by decide
  have hdescent : baseEnd_4091268 < baseStart_4091268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091271 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_4091271 : Nat := 118140960795 + 4091271 * 2 ^ 59
def prefixEnd_4091271 : Nat := 4983230072969 + 3 ^ 40 * 4091271 * 2
def baseEnd_4091271 : Nat := 2100788510800967617097093

theorem tailTrace_4091271 : CollatzResearch.WordTrace tailWord_4091271 prefixEnd_4091271 2100788510800967617097093 := by
  unfold tailWord_4091271
  simp only [CollatzResearch.WordTrace]
  refine ⟨149220912361031375302897667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99480608240687583535265111 149220912361031375302897667)
  ·
    refine ⟨223831368541547062954346501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149220912361031375302897667 223831368541547062954346501)
    ·
      refine ⟨41968381601540074303939969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223831368541547062954346501 41968381601540074303939969)
      ·
        refine ⟨31476286201155055727954977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41968381601540074303939969 31476286201155055727954977)
        ·
          refine ⟨23607214650866291795966233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31476286201155055727954977 23607214650866291795966233)
          ·
            refine ⟨17705410988149718846974675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23607214650866291795966233 17705410988149718846974675)
            ·
              refine ⟨26558116482224578270462013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17705410988149718846974675 26558116482224578270462013)
              ·
                refine ⟨9959293680834216851423255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26558116482224578270462013 9959293680834216851423255)
                ·
                  refine ⟨14938940521251325277134883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9959293680834216851423255 14938940521251325277134883)
                  ·
                    refine ⟨22408410781876987915702325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14938940521251325277134883 22408410781876987915702325)
                    ·
                      refine ⟨2100788510800967617097093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22408410781876987915702325 2100788510800967617097093)
                      ·
                        rfl

theorem cell23_4091271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_4091271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091271 prefixEnd_4091271 := by exact prefixLift 4091271
  have htrace : WordTrace (prefixWord ++ tailWord_4091271) baseStart_4091271 baseEnd_4091271 := by
    simpa [prefixWord, tailWord_4091271, baseEnd_4091271] using wordTrace_append hprefix tailTrace_4091271
  have hstable : (prefixWord ++ tailWord_4091271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091271).length < 2 ^ (prefixWord ++ tailWord_4091271).sum := by decide
  have hdescent : baseEnd_4091271 < baseStart_4091271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091285 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 3, 2, 2]
def baseStart_4091285 : Nat := 118140960795 + 4091285 * 2 ^ 59
def prefixEnd_4091285 : Nat := 4983230072969 + 3 ^ 40 * 4091285 * 2
def baseEnd_4091285 : Nat := 2100795699530130562322029

theorem tailTrace_4091285 : CollatzResearch.WordTrace tailWord_4091285 prefixEnd_4091285 2100795699530130562322029 := by
  unfold tailWord_4091285
  simp only [CollatzResearch.WordTrace]
  refine ⟨149221422982980655693907309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99480948655320437129271539 149221422982980655693907309)
  ·
    refine ⟨55958033618617745885215241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149221422982980655693907309 55958033618617745885215241)
    ·
      refine ⟨41968525213963309413911431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55958033618617745885215241 41968525213963309413911431)
      ·
        refine ⟨62952787820944964120867147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41968525213963309413911431 62952787820944964120867147)
        ·
          refine ⟨94429181731417446181300721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62952787820944964120867147 94429181731417446181300721)
          ·
            refine ⟨70821886298563084635975541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94429181731417446181300721 70821886298563084635975541)
            ·
              refine ⟨6639551840490289184622707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70821886298563084635975541 6639551840490289184622707)
              ·
                refine ⟨9959327760735433776934061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6639551840490289184622707 9959327760735433776934061)
                ·
                  refine ⟨3734747910275787666350273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9959327760735433776934061 3734747910275787666350273)
                  ·
                    refine ⟨2801060932706840749762705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3734747910275787666350273 2801060932706840749762705)
                    ·
                      refine ⟨2100795699530130562322029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801060932706840749762705 2100795699530130562322029)
                      ·
                        rfl

theorem cell23_4091285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_4091285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091285 prefixEnd_4091285 := by exact prefixLift 4091285
  have htrace : WordTrace (prefixWord ++ tailWord_4091285) baseStart_4091285 baseEnd_4091285 := by
    simpa [prefixWord, tailWord_4091285, baseEnd_4091285] using wordTrace_append hprefix tailTrace_4091285
  have hstable : (prefixWord ++ tailWord_4091285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091285).length < 2 ^ (prefixWord ++ tailWord_4091285).sum := by decide
  have hdescent : baseEnd_4091285 < baseStart_4091285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091295 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 2, 4]
def baseStart_4091295 : Nat := 118140960795 + 4091295 * 2 ^ 59
def prefixEnd_4091295 : Nat := 4983230072969 + 3 ^ 40 * 4091295 * 2
def baseEnd_4091295 : Nat := 700266944778891841065661

theorem tailTrace_4091295 : CollatzResearch.WordTrace tailWord_4091295 prefixEnd_4091295 700266944778891841065661 := by
  unfold tailWord_4091295
  simp only [CollatzResearch.WordTrace]
  refine ⟨149221787712944427401771339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99481191808629618267847559 149221787712944427401771339)
  ·
    refine ⟨223832681569416641102657009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149221787712944427401771339 223832681569416641102657009)
    ·
      refine ⟨167874511177062480826992757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223832681569416641102657009 167874511177062480826992757)
      ·
        refine ⟨15738235422849607577530571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167874511177062480826992757 15738235422849607577530571)
        ·
          refine ⟨23607353134274411366295857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15738235422849607577530571 23607353134274411366295857)
          ·
            refine ⟨17705514850705808524721893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23607353134274411366295857 17705514850705808524721893)
            ·
              refine ⟨3319784034507339098385355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17705514850705808524721893 3319784034507339098385355)
              ·
                refine ⟨4979676051761008647578033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319784034507339098385355 4979676051761008647578033)
                ·
                  refine ⟨3734757038820756485683525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979676051761008647578033 3734757038820756485683525)
                  ·
                    refine ⟨700266944778891841065661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3734757038820756485683525 700266944778891841065661)
                    ·
                      rfl

theorem cell23_4091295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 2, 4].length) (baseStart_4091295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091295 prefixEnd_4091295 := by exact prefixLift 4091295
  have htrace : WordTrace (prefixWord ++ tailWord_4091295) baseStart_4091295 baseEnd_4091295 := by
    simpa [prefixWord, tailWord_4091295, baseEnd_4091295] using wordTrace_append hprefix tailTrace_4091295
  have hstable : (prefixWord ++ tailWord_4091295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091295).length < 2 ^ (prefixWord ++ tailWord_4091295).sum := by decide
  have hdescent : baseEnd_4091295 < baseStart_4091295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091335 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_4091335 : Nat := 118140960795 + 4091335 * 2 ^ 59
def prefixEnd_4091335 : Nat := 4983230072969 + 3 ^ 40 * 4091335 * 2
def baseEnd_4091335 : Nat := 2100821373562855366696799

theorem tailTrace_4091335 : CollatzResearch.WordTrace tailWord_4091335 prefixEnd_4091335 2100821373562855366696799 := by
  unfold tailWord_4091335
  simp only [CollatzResearch.WordTrace]
  refine ⟨149223246632799514233227459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99482164421866342822151639 149223246632799514233227459)
  ·
    refine ⟨223834869949199271349841189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149223246632799514233227459 223834869949199271349841189)
    ·
      refine ⟨41969038115474863378095223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223834869949199271349841189 41969038115474863378095223)
      ·
        refine ⟨62953557173212295067142835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41969038115474863378095223 62953557173212295067142835)
        ·
          refine ⟨94430335759818442600714253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62953557173212295067142835 94430335759818442600714253)
          ·
            refine ⟨35411375909931915975267845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94430335759818442600714253 35411375909931915975267845)
            ·
              refine ⟨6639632983112234245362721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35411375909931915975267845 6639632983112234245362721)
              ·
                refine ⟨4979724737334175684022041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6639632983112234245362721 4979724737334175684022041)
                ·
                  refine ⟨3734793553000631763016531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979724737334175684022041 3734793553000631763016531)
                  ·
                    refine ⟨5602190329500947644524797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3734793553000631763016531 5602190329500947644524797)
                    ·
                      refine ⟨2100821373562855366696799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5602190329500947644524797 2100821373562855366696799)
                      ·
                        rfl

theorem cell23_4091335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_4091335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091335 prefixEnd_4091335 := by exact prefixLift 4091335
  have htrace : WordTrace (prefixWord ++ tailWord_4091335) baseStart_4091335 baseEnd_4091335 := by
    simpa [prefixWord, tailWord_4091335, baseEnd_4091335] using wordTrace_append hprefix tailTrace_4091335
  have hstable : (prefixWord ++ tailWord_4091335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091335).length < 2 ^ (prefixWord ++ tailWord_4091335).sum := by decide
  have hdescent : baseEnd_4091335 < baseStart_4091335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091411 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 1, 7]
def baseStart_4091411 : Nat := 118140960795 + 4091411 * 2 ^ 59
def prefixEnd_4091411 : Nat := 4983230072969 + 3 ^ 40 * 4091411 * 2
def baseEnd_4091411 : Nat := 700286799364199023115483

theorem tailTrace_4091411 : CollatzResearch.WordTrace tailWord_4091411 prefixEnd_4091411 700286799364199023115483 := by
  unfold tailWord_4091411
  simp only [CollatzResearch.WordTrace]
  refine ⟨149226018580524179212994087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99484012387016119475329391 149226018580524179212994087)
  ·
    refine ⟨223839027870786268819491131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149226018580524179212994087 223839027870786268819491131)
    ·
      refine ⟨335758541806179403229236697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223839027870786268819491131 335758541806179403229236697)
      ·
        refine ⟨251818906354634552421927523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335758541806179403229236697 251818906354634552421927523)
        ·
          refine ⟨377728359531951828632891285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251818906354634552421927523 377728359531951828632891285)
          ·
            refine ⟨17706016853060241967166779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 377728359531951828632891285 17706016853060241967166779)
            ·
              refine ⟨26559025279590362950750169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17706016853060241967166779 26559025279590362950750169)
              ·
                refine ⟨19919268959692772213062627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26559025279590362950750169 19919268959692772213062627)
                ·
                  refine ⟨29878903439539158319593941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19919268959692772213062627 29878903439539158319593941)
                  ·
                    refine ⟨700286799364199023115483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29878903439539158319593941 700286799364199023115483)
                    ·
                      rfl

theorem cell23_4091411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 7].length) (baseStart_4091411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091411 prefixEnd_4091411 := by exact prefixLift 4091411
  have htrace : WordTrace (prefixWord ++ tailWord_4091411) baseStart_4091411 baseEnd_4091411 := by
    simpa [prefixWord, tailWord_4091411, baseEnd_4091411] using wordTrace_append hprefix tailTrace_4091411
  have hstable : (prefixWord ++ tailWord_4091411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091411).length < 2 ^ (prefixWord ++ tailWord_4091411).sum := by decide
  have hdescent : baseEnd_4091411 < baseStart_4091411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091448 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_4091448 : Nat := 118140960795 + 4091448 * 2 ^ 59
def prefixEnd_4091448 : Nat := 4983230072969 + 3 ^ 40 * 4091448 * 2
def baseEnd_4091448 : Nat := 2100879396876813424583779

theorem tailTrace_4091448 : CollatzResearch.WordTrace tailWord_4091448 prefixEnd_4091448 2100879396876813424583779 := by
  unfold tailWord_4091448
  simp only [CollatzResearch.WordTrace]
  refine ⟨74613684040695067266045499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99484912054260089688060665 74613684040695067266045499)
  ·
    refine ⟨111920526061042600899068249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74613684040695067266045499 111920526061042600899068249)
    ·
      refine ⟨83940394545781950674301187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111920526061042600899068249 83940394545781950674301187)
      ·
        refine ⟨125910591818672926011451781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83940394545781950674301187 125910591818672926011451781)
        ·
          refine ⟨23608235966001173627147209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125910591818672926011451781 23608235966001173627147209)
          ·
            refine ⟨17706176974500880220360407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23608235966001173627147209 17706176974500880220360407)
            ·
              refine ⟨26559265461751320330540611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17706176974500880220360407 26559265461751320330540611)
              ·
                refine ⟨39838898192626980495810917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26559265461751320330540611 39838898192626980495810917)
                ·
                  refine ⟨7469793411117558842964547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39838898192626980495810917 7469793411117558842964547)
                  ·
                    refine ⟨11204690116676338264446821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7469793411117558842964547 11204690116676338264446821)
                    ·
                      refine ⟨2100879396876813424583779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11204690116676338264446821 2100879396876813424583779)
                      ·
                        rfl

theorem cell23_4091448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_4091448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091448 prefixEnd_4091448 := by exact prefixLift 4091448
  have htrace : WordTrace (prefixWord ++ tailWord_4091448) baseStart_4091448 baseEnd_4091448 := by
    simpa [prefixWord, tailWord_4091448, baseEnd_4091448] using wordTrace_append hprefix tailTrace_4091448
  have hstable : (prefixWord ++ tailWord_4091448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091448).length < 2 ^ (prefixWord ++ tailWord_4091448).sum := by decide
  have hdescent : baseEnd_4091448 < baseStart_4091448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091509 : List Nat := [1, 3, 4, 2, 1, 2, 1, 4, 1, 4]
def baseStart_4091509 : Nat := 118140960795 + 4091509 * 2 ^ 59
def prefixEnd_4091509 : Nat := 4983230072969 + 3 ^ 40 * 4091509 * 2
def baseEnd_4091509 : Nat := 700303573065579228640333

theorem tailTrace_4091509 : CollatzResearch.WordTrace tailWord_4091509 prefixEnd_4091509 700303573065579228640333 := by
  unfold tailWord_4091509
  simp only [CollatzResearch.WordTrace]
  refine ⟨149229592934169141950061581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99486395289446094633374387 149229592934169141950061581)
  ·
    refine ⟨55961097350313428231273093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149229592934169141950061581 55961097350313428231273093)
    ·
      refine ⟨10492705753183767793363705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55961097350313428231273093 10492705753183767793363705)
      ·
        refine ⟨7869529314887825845022779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10492705753183767793363705 7869529314887825845022779)
        ·
          refine ⟨11804293972331738767534169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7869529314887825845022779 11804293972331738767534169)
          ·
            refine ⟨8853220479248804075650627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11804293972331738767534169 8853220479248804075650627)
            ·
              refine ⟨13279830718873206113475941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8853220479248804075650627 13279830718873206113475941)
              ·
                refine ⟨2489968259788726146276739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13279830718873206113475941 2489968259788726146276739)
                ·
                  refine ⟨3734952389683089219415109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2489968259788726146276739 3734952389683089219415109)
                  ·
                    refine ⟨700303573065579228640333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3734952389683089219415109 700303573065579228640333)
                    ·
                      rfl

theorem cell23_4091509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_4091509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091509 prefixEnd_4091509 := by exact prefixLift 4091509
  have htrace : WordTrace (prefixWord ++ tailWord_4091509) baseStart_4091509 baseEnd_4091509 := by
    simpa [prefixWord, tailWord_4091509, baseEnd_4091509] using wordTrace_append hprefix tailTrace_4091509
  have hstable : (prefixWord ++ tailWord_4091509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091509).length < 2 ^ (prefixWord ++ tailWord_4091509).sum := by decide
  have hdescent : baseEnd_4091509 < baseStart_4091509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091515 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 3, 1, 3]
def baseStart_4091515 : Nat := 118140960795 + 4091515 * 2 ^ 59
def prefixEnd_4091515 : Nat := 4983230072969 + 3 ^ 40 * 4091515 * 2
def baseEnd_4091515 : Nat := 2100913800080664662445971

theorem tailTrace_4091515 : CollatzResearch.WordTrace tailWord_4091515 prefixEnd_4091515 2100913800080664662445971 := by
  unfold tailWord_4091515
  simp only [CollatzResearch.WordTrace]
  refine ⟨149229811772147404974779999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99486541181431603316519999 149229811772147404974779999)
  ·
    refine ⟨223844717658221107462169999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149229811772147404974779999 223844717658221107462169999)
    ·
      refine ⟨335767076487331661193254999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223844717658221107462169999 335767076487331661193254999)
      ·
        refine ⟨503650614730997491789882499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335767076487331661193254999 503650614730997491789882499)
        ·
          refine ⟨755475922096496237684823749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503650614730997491789882499 755475922096496237684823749)
          ·
            refine ⟨141651735393093044565904453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 755475922096496237684823749 141651735393093044565904453)
            ·
              refine ⟨26559700386204945856107085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141651735393093044565904453 26559700386204945856107085)
              ·
                refine ⟨9959887644826854696040157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26559700386204945856107085 9959887644826854696040157)
                ·
                  refine ⟨3734957866810070511015059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9959887644826854696040157 3734957866810070511015059)
                  ·
                    refine ⟨5602436800215105766522589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3734957866810070511015059 5602436800215105766522589)
                    ·
                      refine ⟨2100913800080664662445971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5602436800215105766522589 2100913800080664662445971)
                      ·
                        rfl

theorem cell23_4091515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 1, 3].length) (baseStart_4091515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091515 prefixEnd_4091515 := by exact prefixLift 4091515
  have htrace : WordTrace (prefixWord ++ tailWord_4091515) baseStart_4091515 baseEnd_4091515 := by
    simpa [prefixWord, tailWord_4091515, baseEnd_4091515] using wordTrace_append hprefix tailTrace_4091515
  have hstable : (prefixWord ++ tailWord_4091515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091515).length < 2 ^ (prefixWord ++ tailWord_4091515).sum := by decide
  have hdescent : baseEnd_4091515 < baseStart_4091515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091525 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 1, 5, 2]
def baseStart_4091525 : Nat := 118140960795 + 4091525 * 2 ^ 59
def prefixEnd_4091525 : Nat := 4983230072969 + 3 ^ 40 * 4091525 * 2
def baseEnd_4091525 : Nat := 2100918934887209623320925

theorem tailTrace_4091525 : CollatzResearch.WordTrace tailWord_4091525 prefixEnd_4091525 2100918934887209623320925 := by
  unfold tailWord_4091525
  simp only [CollatzResearch.WordTrace]
  refine ⟨149230176502111176682644029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99486784334740784455096019 149230176502111176682644029)
  ·
    refine ⟨55961316188291691255991511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149230176502111176682644029 55961316188291691255991511)
    ·
      refine ⟨83941974282437536883987267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55961316188291691255991511 83941974282437536883987267)
      ·
        refine ⟨125912961423656305325980901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83941974282437536883987267 125912961423656305325980901)
        ·
          refine ⟨23608680266935557248621419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125912961423656305325980901 23608680266935557248621419)
          ·
            refine ⟨35413020400403335872932129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23608680266935557248621419 35413020400403335872932129)
            ·
              refine ⟨26559765300302501904699097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35413020400403335872932129 26559765300302501904699097)
              ·
                refine ⟨19919823975226876428524323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26559765300302501904699097 19919823975226876428524323)
                ·
                  refine ⟨29879735962840314642786485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19919823975226876428524323 29879735962840314642786485)
                  ·
                    refine ⟨2801225246516279497761233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29879735962840314642786485 2801225246516279497761233)
                    ·
                      refine ⟨2100918934887209623320925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801225246516279497761233 2100918934887209623320925)
                      ·
                        rfl

theorem cell23_4091525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 5, 2].length) (baseStart_4091525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091525 prefixEnd_4091525 := by exact prefixLift 4091525
  have htrace : WordTrace (prefixWord ++ tailWord_4091525) baseStart_4091525 baseEnd_4091525 := by
    simpa [prefixWord, tailWord_4091525, baseEnd_4091525] using wordTrace_append hprefix tailTrace_4091525
  have hstable : (prefixWord ++ tailWord_4091525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091525).length < 2 ^ (prefixWord ++ tailWord_4091525).sum := by decide
  have hdescent : baseEnd_4091525 < baseStart_4091525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091552 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 1, 5]
def baseStart_4091552 : Nat := 118140960795 + 4091552 * 2 ^ 59
def prefixEnd_4091552 : Nat := 4983230072969 + 3 ^ 40 * 4091552 * 2
def baseEnd_4091552 : Nat := 700310932954960339227767

theorem tailTrace_4091552 : CollatzResearch.WordTrace tailWord_4091552 prefixEnd_4091552 700310932954960339227767 := by
  unfold tailWord_4091552
  simp only [CollatzResearch.WordTrace]
  refine ⟨74615580636506680146938455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99487440848675573529251273 74615580636506680146938455)
  ·
    refine ⟨111923370954760020220407683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74615580636506680146938455 111923370954760020220407683)
    ·
      refine ⟨167885056432140030330611525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111923370954760020220407683 167885056432140030330611525)
      ·
        refine ⟨31478448081026255686989661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167885056432140030330611525 31478448081026255686989661)
        ·
          refine ⟨11804418030384845882621123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31478448081026255686989661 11804418030384845882621123)
          ·
            refine ⟨17706627045577268823931685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11804418030384845882621123 17706627045577268823931685)
            ·
              refine ⟨3319992571045737904487191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17706627045577268823931685 3319992571045737904487191)
              ·
                refine ⟨4979988856568606856730787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319992571045737904487191 4979988856568606856730787)
                ·
                  refine ⟨7469983284852910285096181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979988856568606856730787 7469983284852910285096181)
                  ·
                    refine ⟨700310932954960339227767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7469983284852910285096181 700310932954960339227767)
                    ·
                      rfl

theorem cell23_4091552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 5].length) (baseStart_4091552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091552 prefixEnd_4091552 := by exact prefixLift 4091552
  have htrace : WordTrace (prefixWord ++ tailWord_4091552) baseStart_4091552 baseEnd_4091552 := by
    simpa [prefixWord, tailWord_4091552, baseEnd_4091552] using wordTrace_append hprefix tailTrace_4091552
  have hstable : (prefixWord ++ tailWord_4091552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091552).length < 2 ^ (prefixWord ++ tailWord_4091552).sum := by decide
  have hdescent : baseEnd_4091552 < baseStart_4091552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091555 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 4]
def baseStart_4091555 : Nat := 118140960795 + 4091555 * 2 ^ 59
def prefixEnd_4091555 : Nat := 4983230072969 + 3 ^ 40 * 4091555 * 2
def baseEnd_4091555 : Nat := 2100934339306844505945787

theorem tailTrace_4091555 : CollatzResearch.WordTrace tailWord_4091555 prefixEnd_4091555 2100934339306844505945787 := by
  unfold tailWord_4091555
  simp only [CollatzResearch.WordTrace]
  refine ⟨149231270692002491806236119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99487513794668327870824079 149231270692002491806236119)
  ·
    refine ⟨223846906038003737709354179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149231270692002491806236119 223846906038003737709354179)
    ·
      refine ⟨335770359057005606564031269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223846906038003737709354179 335770359057005606564031269)
      ·
        refine ⟨62956942323188551230755863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335770359057005606564031269 62956942323188551230755863)
        ·
          refine ⟨94435413484782826846133795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62956942323188551230755863 94435413484782826846133795)
          ·
            refine ⟨141653120227174240269200693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94435413484782826846133795 141653120227174240269200693)
            ·
              refine ⟨13279980021297585025237565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141653120227174240269200693 13279980021297585025237565)
              ·
                refine ⟨4979992507986594384464087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13279980021297585025237565 4979992507986594384464087)
                ·
                  refine ⟨7469988761979891576696131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979992507986594384464087 7469988761979891576696131)
                  ·
                    refine ⟨11204983142969837365044197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7469988761979891576696131 11204983142969837365044197)
                    ·
                      refine ⟨2100934339306844505945787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11204983142969837365044197 2100934339306844505945787)
                      ·
                        rfl

theorem cell23_4091555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_4091555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091555 prefixEnd_4091555 := by exact prefixLift 4091555
  have htrace : WordTrace (prefixWord ++ tailWord_4091555) baseStart_4091555 baseEnd_4091555 := by
    simpa [prefixWord, tailWord_4091555, baseEnd_4091555] using wordTrace_append hprefix tailTrace_4091555
  have hstable : (prefixWord ++ tailWord_4091555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091555).length < 2 ^ (prefixWord ++ tailWord_4091555).sum := by decide
  have hdescent : baseEnd_4091555 < baseStart_4091555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091566 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_4091566 : Nat := 118140960795 + 4091566 * 2 ^ 59
def prefixEnd_4091566 : Nat := 4983230072969 + 3 ^ 40 * 4091566 * 2
def baseEnd_4091566 : Nat := 2100939987594043962908237

theorem tailTrace_4091566 : CollatzResearch.WordTrace tailWord_4091566 prefixEnd_4091566 2100939987594043962908237 := by
  unfold tailWord_4091566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18653958986870330085610819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99487781263308427123257701 18653958986870330085610819)
  ·
    refine ⟨27980938480305495128416229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18653958986870330085610819 27980938480305495128416229)
    ·
      refine ⟨5246425965057280336578043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27980938480305495128416229 5246425965057280336578043)
      ·
        refine ⟨7869638947585920504867065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5246425965057280336578043 7869638947585920504867065)
        ·
          refine ⟨5902229210689440378650299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7869638947585920504867065 5902229210689440378650299)
          ·
            refine ⟨8853343816034160567975449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5902229210689440378650299 8853343816034160567975449)
            ·
              refine ⟨6640007862025620425981587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8853343816034160567975449 6640007862025620425981587)
              ·
                refine ⟨9960011793038430638972381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640007862025620425981587 9960011793038430638972381)
                ·
                  refine ⟨3735004422389411489614643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9960011793038430638972381 3735004422389411489614643)
                  ·
                    refine ⟨5602506633584117234421965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3735004422389411489614643 5602506633584117234421965)
                    ·
                      refine ⟨2100939987594043962908237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5602506633584117234421965 2100939987594043962908237)
                      ·
                        rfl

theorem cell23_4091566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_4091566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091566 prefixEnd_4091566 := by exact prefixLift 4091566
  have htrace : WordTrace (prefixWord ++ tailWord_4091566) baseStart_4091566 baseEnd_4091566 := by
    simpa [prefixWord, tailWord_4091566, baseEnd_4091566] using wordTrace_append hprefix tailTrace_4091566
  have hstable : (prefixWord ++ tailWord_4091566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091566).length < 2 ^ (prefixWord ++ tailWord_4091566).sum := by decide
  have hdescent : baseEnd_4091566 < baseStart_4091566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091568 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 4]
def baseStart_4091568 : Nat := 118140960795 + 4091568 * 2 ^ 59
def prefixEnd_4091568 : Nat := 4983230072969 + 3 ^ 40 * 4091568 * 2
def baseEnd_4091568 : Nat := 2100941014555352955083227

theorem tailTrace_4091568 : CollatzResearch.WordTrace tailWord_4091568 prefixEnd_4091568 2100941014555352955083227 := by
  unfold tailWord_4091568
  simp only [CollatzResearch.WordTrace]
  refine ⟨74615872420477697513229679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99487829893970263350972905 74615872420477697513229679)
  ·
    refine ⟨111923808630716546269844519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74615872420477697513229679 111923808630716546269844519)
    ·
      refine ⟨167885712946074819404766779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111923808630716546269844519 167885712946074819404766779)
      ·
        refine ⟨251828569419112229107150169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167885712946074819404766779 251828569419112229107150169)
        ·
          refine ⟨188871427064334171830362627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251828569419112229107150169 188871427064334171830362627)
          ·
            refine ⟨283307140596501257745543941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188871427064334171830362627 283307140596501257745543941)
            ·
              refine ⟨53120088861843985827289489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283307140596501257745543941 53120088861843985827289489)
              ·
                refine ⟨39840066646382989370467117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53120088861843985827289489 39840066646382989370467117)
                ·
                  refine ⟨14940024992393621013925169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39840066646382989370467117 14940024992393621013925169)
                  ·
                    refine ⟨11205018744295215760443877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14940024992393621013925169 11205018744295215760443877)
                    ·
                      refine ⟨2100941014555352955083227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11205018744295215760443877 2100941014555352955083227)
                      ·
                        rfl

theorem cell23_4091568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_4091568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091568 prefixEnd_4091568 := by exact prefixLift 4091568
  have htrace : WordTrace (prefixWord ++ tailWord_4091568) baseStart_4091568 baseEnd_4091568 := by
    simpa [prefixWord, tailWord_4091568, baseEnd_4091568] using wordTrace_append hprefix tailTrace_4091568
  have hstable : (prefixWord ++ tailWord_4091568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091568).length < 2 ^ (prefixWord ++ tailWord_4091568).sum := by decide
  have hdescent : baseEnd_4091568 < baseStart_4091568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091575 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_4091575 : Nat := 118140960795 + 4091575 * 2 ^ 59
def prefixEnd_4091575 : Nat := 4983230072969 + 3 ^ 40 * 4091575 * 2
def baseEnd_4091575 : Nat := 2100944608919934427695695

theorem tailTrace_4091575 : CollatzResearch.WordTrace tailWord_4091575 prefixEnd_4091575 2100944608919934427695695 := by
  unfold tailWord_4091575
  simp only [CollatzResearch.WordTrace]
  refine ⟨149232000151930035221964179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99488000101286690147976119 149232000151930035221964179)
  ·
    refine ⟨223848000227895052832946269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149232000151930035221964179 223848000227895052832946269)
    ·
      refine ⟨83943000085460644812354851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223848000227895052832946269 83943000085460644812354851)
      ·
        refine ⟨125914500128190967218532277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83943000085460644812354851 125914500128190967218532277)
        ·
          refine ⟨11804484387017903176737401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125914500128190967218532277 11804484387017903176737401)
          ·
            refine ⟨8853363290263427382553051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11804484387017903176737401 8853363290263427382553051)
            ·
              refine ⟨13280044935395141073829577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8853363290263427382553051 13280044935395141073829577)
              ·
                refine ⟨9960033701546355805372183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13280044935395141073829577 9960033701546355805372183)
                ·
                  refine ⟨14940050552319533708058275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9960033701546355805372183 14940050552319533708058275)
                  ·
                    refine ⟨22410075828479300562087413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14940050552319533708058275 22410075828479300562087413)
                    ·
                      refine ⟨2100944608919934427695695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22410075828479300562087413 2100944608919934427695695)
                      ·
                        rfl

theorem cell23_4091575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_4091575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091575 prefixEnd_4091575 := by exact prefixLift 4091575
  have htrace : WordTrace (prefixWord ++ tailWord_4091575) baseStart_4091575 baseEnd_4091575 := by
    simpa [prefixWord, tailWord_4091575, baseEnd_4091575] using wordTrace_append hprefix tailTrace_4091575
  have hstable : (prefixWord ++ tailWord_4091575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091575).length < 2 ^ (prefixWord ++ tailWord_4091575).sum := by decide
  have hdescent : baseEnd_4091575 < baseStart_4091575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091582 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_4091582 : Nat := 118140960795 + 4091582 * 2 ^ 59
def prefixEnd_4091582 : Nat := 4983230072969 + 3 ^ 40 * 4091582 * 2
def baseEnd_4091582 : Nat := 700316067761505300102721

theorem tailTrace_4091582 : CollatzResearch.WordTrace tailWord_4091582 prefixEnd_4091582 700316067761505300102721 := by
  unfold tailWord_4091582
  simp only [CollatzResearch.WordTrace]
  refine ⟨18654031932863084427183625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99488170308603116944979333 18654031932863084427183625)
  ·
    refine ⟨13990523949647313320387719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18654031932863084427183625 13990523949647313320387719)
    ·
      refine ⟨20985785924470969980581579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13990523949647313320387719 20985785924470969980581579)
      ·
        refine ⟨31478678886706454970872369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20985785924470969980581579 31478678886706454970872369)
        ·
          refine ⟨23609009165029841228154277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31478678886706454970872369 23609009165029841228154277)
          ·
            refine ⟨4426689218443095230278927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23609009165029841228154277 4426689218443095230278927)
            ·
              refine ⟨6640033827664642845418391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426689218443095230278927 6640033827664642845418391)
              ·
                refine ⟨9960050741496964268127587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640033827664642845418391 9960050741496964268127587)
                ·
                  refine ⟨14940076112245446402191381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9960050741496964268127587 14940076112245446402191381)
                  ·
                    refine ⟨700316067761505300102721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14940076112245446402191381 700316067761505300102721)
                    ·
                      rfl

theorem cell23_4091582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_4091582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091582 prefixEnd_4091582 := by exact prefixLift 4091582
  have htrace : WordTrace (prefixWord ++ tailWord_4091582) baseStart_4091582 baseEnd_4091582 := by
    simpa [prefixWord, tailWord_4091582, baseEnd_4091582] using wordTrace_append hprefix tailTrace_4091582
  have hstable : (prefixWord ++ tailWord_4091582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091582).length < 2 ^ (prefixWord ++ tailWord_4091582).sum := by decide
  have hdescent : baseEnd_4091582 < baseStart_4091582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091592 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_4091592 : Nat := 118140960795 + 4091592 * 2 ^ 59
def prefixEnd_4091592 : Nat := 4983230072969 + 3 ^ 40 * 4091592 * 2
def baseEnd_4091592 : Nat := 2100953338091060861183117

theorem tailTrace_4091592 : CollatzResearch.WordTrace tailWord_4091592 prefixEnd_4091592 2100953338091060861183117 := by
  unfold tailWord_4091592
  simp only [CollatzResearch.WordTrace]
  refine ⟨74616310096434223562666515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99488413461912298083555353 74616310096434223562666515)
  ·
    refine ⟨111924465144651335343999773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74616310096434223562666515 111924465144651335343999773)
    ·
      refine ⟨41971674429244250753999915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111924465144651335343999773 41971674429244250753999915)
      ·
        refine ⟨62957511643866376130999873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41971674429244250753999915 62957511643866376130999873)
        ·
          refine ⟨47218133732899782098249905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62957511643866376130999873 47218133732899782098249905)
          ·
            refine ⟨35413600299674836573687429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47218133732899782098249905 35413600299674836573687429)
            ·
              refine ⟨6640050056189031857566393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35413600299674836573687429 6640050056189031857566393)
              ·
                refine ⟨4980037542141773893174795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6640050056189031857566393 4980037542141773893174795)
                ·
                  refine ⟨7470056313212660839762193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980037542141773893174795 7470056313212660839762193)
                  ·
                    refine ⟨5602542234909495629821645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7470056313212660839762193 5602542234909495629821645)
                    ·
                      refine ⟨2100953338091060861183117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5602542234909495629821645 2100953338091060861183117)
                      ·
                        rfl

theorem cell23_4091592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_4091592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091592 prefixEnd_4091592 := by exact prefixLift 4091592
  have htrace : WordTrace (prefixWord ++ tailWord_4091592) baseStart_4091592 baseEnd_4091592 := by
    simpa [prefixWord, tailWord_4091592, baseEnd_4091592] using wordTrace_append hprefix tailTrace_4091592
  have hstable : (prefixWord ++ tailWord_4091592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091592).length < 2 ^ (prefixWord ++ tailWord_4091592).sum := by decide
  have hdescent : baseEnd_4091592 < baseStart_4091592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091612 : List Nat := [2, 2, 5, 1, 2, 2, 9]
def baseStart_4091612 : Nat := 118140960795 + 4091612 * 2 ^ 59
def prefixEnd_4091612 : Nat := 4983230072969 + 3 ^ 40 * 4091612 * 2
def baseEnd_4091612 : Nat := 25937822317335194851025

theorem tailTrace_4091612 : CollatzResearch.WordTrace tailWord_4091612 prefixEnd_4091612 25937822317335194851025 := by
  unfold tailWord_4091612
  simp only [CollatzResearch.WordTrace]
  refine ⟨74616674826397995270530545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99488899768530660360707393 74616674826397995270530545)
  ·
    refine ⟨55962506119798496452897909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74616674826397995270530545 55962506119798496452897909)
    ·
      refine ⟨5246484948731109042459179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55962506119798496452897909 5246484948731109042459179)
      ·
        refine ⟨7869727423096663563688769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5246484948731109042459179 7869727423096663563688769)
        ·
          refine ⟨5902295567322497672766577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7869727423096663563688769 5902295567322497672766577)
          ·
            refine ⟨4426721675491873254574933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5902295567322497672766577 4426721675491873254574933)
            ·
              refine ⟨25937822317335194851025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4426721675491873254574933 25937822317335194851025)
              ·
                rfl

theorem cell23_4091612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 9].length) (baseStart_4091612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091612 prefixEnd_4091612 := by exact prefixLift 4091612
  have htrace : WordTrace (prefixWord ++ tailWord_4091612) baseStart_4091612 baseEnd_4091612 := by
    simpa [prefixWord, tailWord_4091612, baseEnd_4091612] using wordTrace_append hprefix tailTrace_4091612
  have hstable : (prefixWord ++ tailWord_4091612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091612).length < 2 ^ (prefixWord ++ tailWord_4091612).sum := by decide
  have hdescent : baseEnd_4091612 < baseStart_4091612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091623 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4091623 : Nat := 118140960795 + 4091623 * 2 ^ 59
def prefixEnd_4091623 : Nat := 4983230072969 + 3 ^ 40 * 4091623 * 2
def baseEnd_4091623 : Nat := 2100969255991350239895475

theorem tailTrace_4091623 : CollatzResearch.WordTrace tailWord_4091623 prefixEnd_4091623 2100969255991350239895475 := by
  unfold tailWord_4091623
  simp only [CollatzResearch.WordTrace]
  refine ⟨149233750855756139419711523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99489167237170759613141015 149233750855756139419711523)
  ·
    refine ⟨223850626283634209129567285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149233750855756139419711523 223850626283634209129567285)
    ·
      refine ⟨20985996214090707105896933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223850626283634209129567285 20985996214090707105896933)
      ·
        refine ⟨3934874290142007582355675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20985996214090707105896933 3934874290142007582355675)
        ·
          refine ⟨5902311435213011373533513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3934874290142007582355675 5902311435213011373533513)
          ·
            refine ⟨4426733576409758530150135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5902311435213011373533513 4426733576409758530150135)
            ·
              refine ⟨6640100364614637795225203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426733576409758530150135 6640100364614637795225203)
              ·
                refine ⟨9960150546921956692837805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640100364614637795225203 9960150546921956692837805)
                ·
                  refine ⟨3735056455095733759814177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9960150546921956692837805 3735056455095733759814177)
                  ·
                    refine ⟨2801292341321800319860633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3735056455095733759814177 2801292341321800319860633)
                    ·
                      refine ⟨2100969255991350239895475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801292341321800319860633 2100969255991350239895475)
                      ·
                        rfl

theorem cell23_4091623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4091623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091623 prefixEnd_4091623 := by exact prefixLift 4091623
  have htrace : WordTrace (prefixWord ++ tailWord_4091623) baseStart_4091623 baseEnd_4091623 := by
    simpa [prefixWord, tailWord_4091623, baseEnd_4091623] using wordTrace_append hprefix tailTrace_4091623
  have hstable : (prefixWord ++ tailWord_4091623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091623).length < 2 ^ (prefixWord ++ tailWord_4091623).sum := by decide
  have hdescent : baseEnd_4091623 < baseStart_4091623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091639 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 2, 1, 3]
def baseStart_4091639 : Nat := 118140960795 + 4091639 * 2 ^ 59
def prefixEnd_4091639 : Nat := 4983230072969 + 3 ^ 40 * 4091639 * 2
def baseEnd_4091639 : Nat := 2100977471681822177295401

theorem tailTrace_4091639 : CollatzResearch.WordTrace tailWord_4091639 prefixEnd_4091639 2100977471681822177295401 := by
  unfold tailWord_4091639
  simp only [CollatzResearch.WordTrace]
  refine ⟨149234334423698174152293971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99489556282465449434862647 149234334423698174152293971)
  ·
    refine ⟨223851501635547261228440957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149234334423698174152293971 223851501635547261228440957)
    ·
      refine ⟨83944313113330222960665359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223851501635547261228440957 83944313113330222960665359)
      ·
        refine ⟨125916469669995334440998039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83944313113330222960665359 125916469669995334440998039)
        ·
          refine ⟨188874704504993001661497059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125916469669995334440998039 188874704504993001661497059)
          ·
            refine ⟨283312056757489502492245589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188874704504993001661497059 283312056757489502492245589)
            ·
              refine ⟨3320063165126830107331003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 283312056757489502492245589 3320063165126830107331003)
              ·
                refine ⟨4980094747690245160996505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320063165126830107331003 4980094747690245160996505)
                ·
                  refine ⟨3735071060767683870747379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4980094747690245160996505 3735071060767683870747379)
                  ·
                    refine ⟨5602606591151525806121069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3735071060767683870747379 5602606591151525806121069)
                    ·
                      refine ⟨2100977471681822177295401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5602606591151525806121069 2100977471681822177295401)
                      ·
                        rfl

theorem cell23_4091639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 2, 1, 3].length) (baseStart_4091639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091639 prefixEnd_4091639 := by exact prefixLift 4091639
  have htrace : WordTrace (prefixWord ++ tailWord_4091639) baseStart_4091639 baseEnd_4091639 := by
    simpa [prefixWord, tailWord_4091639, baseEnd_4091639] using wordTrace_append hprefix tailTrace_4091639
  have hstable : (prefixWord ++ tailWord_4091639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091639).length < 2 ^ (prefixWord ++ tailWord_4091639).sum := by decide
  have hdescent : baseEnd_4091639 < baseStart_4091639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091648 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_4091648 : Nat := 118140960795 + 4091648 * 2 ^ 59
def prefixEnd_4091648 : Nat := 4983230072969 + 3 ^ 40 * 4091648 * 2
def baseEnd_4091648 : Nat := 2100982093007712642082859

theorem tailTrace_4091648 : CollatzResearch.WordTrace tailWord_4091648 prefixEnd_4091648 2100982093007712642082859 := by
  unfold tailWord_4091648
  simp only [CollatzResearch.WordTrace]
  refine ⟨74617331340332784344685799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99489775120443712459581065 74617331340332784344685799)
  ·
    refine ⟨111925997010499176517028699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74617331340332784344685799 111925997010499176517028699)
    ·
      refine ⟨167888995515748764775543049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111925997010499176517028699 167888995515748764775543049)
      ·
        refine ⟨125916746636811573581657287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167888995515748764775543049 125916746636811573581657287)
        ·
          refine ⟨188875119955217360372485931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125916746636811573581657287 188875119955217360372485931)
          ·
            refine ⟨283312679932826040558728897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188875119955217360372485931 283312679932826040558728897)
            ·
              refine ⟨212484509949619530419046673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283312679932826040558728897 212484509949619530419046673)
              ·
                refine ⟨159363382462214647814285005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212484509949619530419046673 159363382462214647814285005)
                ·
                  refine ⟨59761268423330492930356877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159363382462214647814285005 59761268423330492930356877)
                  ·
                    refine ⟨22410475658748934848883829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59761268423330492930356877 22410475658748934848883829)
                    ·
                      refine ⟨2100982093007712642082859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22410475658748934848883829 2100982093007712642082859)
                      ·
                        rfl

theorem cell23_4091648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_4091648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091648 prefixEnd_4091648 := by exact prefixLift 4091648
  have htrace : WordTrace (prefixWord ++ tailWord_4091648) baseStart_4091648 baseEnd_4091648 := by
    simpa [prefixWord, tailWord_4091648, baseEnd_4091648] using wordTrace_append hprefix tailTrace_4091648
  have hstable : (prefixWord ++ tailWord_4091648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091648).length < 2 ^ (prefixWord ++ tailWord_4091648).sum := by decide
  have hdescent : baseEnd_4091648 < baseStart_4091648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091649 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_4091649 : Nat := 118140960795 + 4091649 * 2 ^ 59
def prefixEnd_4091649 : Nat := 4983230072969 + 3 ^ 40 * 4091649 * 2
def baseEnd_4091649 : Nat := 2100982606488367138170355

theorem tailTrace_4091649 : CollatzResearch.WordTrace tailWord_4091649 prefixEnd_4091649 2100982606488367138170355 := by
  unfold tailWord_4091649
  simp only [CollatzResearch.WordTrace]
  refine ⟨149234699153661945860158001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99489799435774630573438667 149234699153661945860158001)
  ·
    refine ⟨111926024365246459395118501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149234699153661945860158001 111926024365246459395118501)
    ·
      refine ⟨20986129568483711136584719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111926024365246459395118501 20986129568483711136584719)
      ·
        refine ⟨31479194352725566704877079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20986129568483711136584719 31479194352725566704877079)
        ·
          refine ⟨47218791529088350057315619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31479194352725566704877079 47218791529088350057315619)
          ·
            refine ⟨70828187293632525085973429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47218791529088350057315619 70828187293632525085973429)
            ·
              refine ⟨6640142558778049226810009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70828187293632525085973429 6640142558778049226810009)
              ·
                refine ⟨4980106919083536920107507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6640142558778049226810009 4980106919083536920107507)
                ·
                  refine ⟨7470160378625305380161261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980106919083536920107507 7470160378625305380161261)
                  ·
                    refine ⟨2801310141984489517560473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7470160378625305380161261 2801310141984489517560473)
                    ·
                      refine ⟨2100982606488367138170355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801310141984489517560473 2100982606488367138170355)
                      ·
                        rfl

theorem cell23_4091649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_4091649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091649 prefixEnd_4091649 := by exact prefixLift 4091649
  have htrace : WordTrace (prefixWord ++ tailWord_4091649) baseStart_4091649 baseEnd_4091649 := by
    simpa [prefixWord, tailWord_4091649, baseEnd_4091649] using wordTrace_append hprefix tailTrace_4091649
  have hstable : (prefixWord ++ tailWord_4091649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091649).length < 2 ^ (prefixWord ++ tailWord_4091649).sum := by decide
  have hdescent : baseEnd_4091649 < baseStart_4091649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091662 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2]
def baseStart_4091662 : Nat := 118140960795 + 4091662 * 2 ^ 59
def prefixEnd_4091662 : Nat := 4983230072969 + 3 ^ 40 * 4091662 * 2
def baseEnd_4091662 : Nat := 2100989281736875587307795

theorem tailTrace_4091662 : CollatzResearch.WordTrace tailWord_4091662 prefixEnd_4091662 2100989281736875587307795 := by
  unfold tailWord_4091662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18654396662826856135047655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99490115535076566053587493 18654396662826856135047655)
  ·
    refine ⟨27981594994240284202571483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18654396662826856135047655 27981594994240284202571483)
    ·
      refine ⟨41972392491360426303857225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27981594994240284202571483 41972392491360426303857225)
      ·
        refine ⟨31479294368520319727892919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41972392491360426303857225 31479294368520319727892919)
        ·
          refine ⟨47218941552780479591839379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31479294368520319727892919 47218941552780479591839379)
          ·
            refine ⟨70828412329170719387759069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47218941552780479591839379 70828412329170719387759069)
            ·
              refine ⟨26560654623439019770409651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70828412329170719387759069 26560654623439019770409651)
              ·
                refine ⟨39840981935158529655614477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26560654623439019770409651 39840981935158529655614477)
                ·
                  refine ⟨14940368225684448620855429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39840981935158529655614477 14940368225684448620855429)
                  ·
                    refine ⟨2801319042315834116410393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14940368225684448620855429 2801319042315834116410393)
                    ·
                      refine ⟨2100989281736875587307795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801319042315834116410393 2100989281736875587307795)
                      ·
                        rfl

theorem cell23_4091662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_4091662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091662 prefixEnd_4091662 := by exact prefixLift 4091662
  have htrace : WordTrace (prefixWord ++ tailWord_4091662) baseStart_4091662 baseEnd_4091662 := by
    simpa [prefixWord, tailWord_4091662, baseEnd_4091662] using wordTrace_append hprefix tailTrace_4091662
  have hstable : (prefixWord ++ tailWord_4091662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091662).length < 2 ^ (prefixWord ++ tailWord_4091662).sum := by decide
  have hdescent : baseEnd_4091662 < baseStart_4091662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091695 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 3]
def baseStart_4091695 : Nat := 118140960795 + 4091695 * 2 ^ 59
def prefixEnd_4091695 : Nat := 4983230072969 + 3 ^ 40 * 4091695 * 2
def baseEnd_4091695 : Nat := 2101006226598473958195143

theorem tailTrace_4091695 : CollatzResearch.WordTrace tailWord_4091695 prefixEnd_4091695 2101006226598473958195143 := by
  unfold tailWord_4091695
  simp only [CollatzResearch.WordTrace]
  refine ⟨149236376911495295716332539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99490917940996863810888359 149236376911495295716332539)
  ·
    refine ⟨223854565367242943574498809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149236376911495295716332539 223854565367242943574498809)
    ·
      refine ⟨167890924025432207680874107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223854565367242943574498809 167890924025432207680874107)
      ·
        refine ⟨251836386038148311521311161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167890924025432207680874107 251836386038148311521311161)
        ·
          refine ⟨188877289528611233640983371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251836386038148311521311161 188877289528611233640983371)
          ·
            refine ⟨283315934292916850461475057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188877289528611233640983371 283315934292916850461475057)
            ·
              refine ⟨212486950719687637846106293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283315934292916850461475057 212486950719687637846106293)
              ·
                refine ⟨19920651629970716048072465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212486950719687637846106293 19920651629970716048072465)
                ·
                  refine ⟨14940488722478037036054349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19920651629970716048072465 14940488722478037036054349)
                  ·
                    refine ⟨5602683270929263888520381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14940488722478037036054349 5602683270929263888520381)
                    ·
                      refine ⟨2101006226598473958195143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5602683270929263888520381 2101006226598473958195143)
                      ·
                        rfl

theorem cell23_4091695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 3].length) (baseStart_4091695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091695 prefixEnd_4091695 := by exact prefixLift 4091695
  have htrace : WordTrace (prefixWord ++ tailWord_4091695) baseStart_4091695 baseEnd_4091695 := by
    simpa [prefixWord, tailWord_4091695, baseEnd_4091695] using wordTrace_append hprefix tailTrace_4091695
  have hstable : (prefixWord ++ tailWord_4091695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091695).length < 2 ^ (prefixWord ++ tailWord_4091695).sum := by decide
  have hdescent : baseEnd_4091695 < baseStart_4091695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091702 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_4091702 : Nat := 118140960795 + 4091702 * 2 ^ 59
def prefixEnd_4091702 : Nat := 4983230072969 + 3 ^ 40 * 4091702 * 2
def baseEnd_4091702 : Nat := 233445535662561714534179

theorem tailTrace_4091702 : CollatzResearch.WordTrace tailWord_4091702 prefixEnd_4091702 233445535662561714534179 := by
  unfold tailWord_4091702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9327289513904370994489835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99491088148313290607891573 9327289513904370994489835)
  ·
    refine ⟨13990934270856556491734753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9327289513904370994489835 13990934270856556491734753)
    ·
      refine ⟨10493200703142417368801065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13990934270856556491734753 10493200703142417368801065)
      ·
        refine ⟨7869900527356813026600799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10493200703142417368801065 7869900527356813026600799)
        ·
          refine ⟨11804850791035219539901199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7869900527356813026600799 11804850791035219539901199)
          ·
            refine ⟨17707276186552829309851799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11804850791035219539901199 17707276186552829309851799)
            ·
              refine ⟨26560914279829243964777699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17707276186552829309851799 26560914279829243964777699)
              ·
                refine ⟨39841371419743865947166549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26560914279829243964777699 39841371419743865947166549)
                ·
                  refine ⟨233445535662561714534179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39841371419743865947166549 233445535662561714534179)
                  ·
                    rfl

theorem cell23_4091702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_4091702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091702 prefixEnd_4091702 := by exact prefixLift 4091702
  have htrace : WordTrace (prefixWord ++ tailWord_4091702) baseStart_4091702 baseEnd_4091702 := by
    simpa [prefixWord, tailWord_4091702, baseEnd_4091702] using wordTrace_append hprefix tailTrace_4091702
  have hstable : (prefixWord ++ tailWord_4091702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091702).length < 2 ^ (prefixWord ++ tailWord_4091702).sum := by decide
  have hdescent : baseEnd_4091702 < baseStart_4091702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091715 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 1, 7]
def baseStart_4091715 : Nat := 118140960795 + 4091715 * 2 ^ 59
def prefixEnd_4091715 : Nat := 4983230072969 + 3 ^ 40 * 4091715 * 2
def baseEnd_4091715 : Nat := 700338832070521293315017

theorem tailTrace_4091715 : CollatzResearch.WordTrace tailWord_4091715 prefixEnd_4091715 700338832070521293315017 := by
  unfold tailWord_4091715
  simp only [CollatzResearch.WordTrace]
  refine ⟨149237106371422839132060599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99491404247615226088040399 149237106371422839132060599)
  ·
    refine ⟨223855659557134258698090899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149237106371422839132060599 223855659557134258698090899)
    ·
      refine ⟨335783489335701388047136349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223855659557134258698090899 335783489335701388047136349)
      ·
        refine ⟨125918808500888020517676131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335783489335701388047136349 125918808500888020517676131)
        ·
          refine ⟨188878212751332030776514197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125918808500888020517676131 188878212751332030776514197)
          ·
            refine ⟨8853666222718688942649103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188878212751332030776514197 8853666222718688942649103)
            ·
              refine ⟨13280499334078033413973655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8853666222718688942649103 13280499334078033413973655)
              ·
                refine ⟨19920749001117050120960483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13280499334078033413973655 19920749001117050120960483)
                ·
                  refine ⟨29881123501675575181440725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19920749001117050120960483 29881123501675575181440725)
                  ·
                    refine ⟨700338832070521293315017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29881123501675575181440725 700338832070521293315017)
                    ·
                      rfl

theorem cell23_4091715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 7].length) (baseStart_4091715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091715 prefixEnd_4091715 := by exact prefixLift 4091715
  have htrace : WordTrace (prefixWord ++ tailWord_4091715) baseStart_4091715 baseEnd_4091715 := by
    simpa [prefixWord, tailWord_4091715, baseEnd_4091715] using wordTrace_append hprefix tailTrace_4091715
  have hstable : (prefixWord ++ tailWord_4091715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091715).length < 2 ^ (prefixWord ++ tailWord_4091715).sum := by decide
  have hdescent : baseEnd_4091715 < baseStart_4091715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091796 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_4091796 : Nat := 118140960795 + 4091796 * 2 ^ 59
def prefixEnd_4091796 : Nat := 4983230072969 + 3 ^ 40 * 4091796 * 2
def baseEnd_4091796 : Nat := 700352696048192687677393

theorem tailTrace_4091796 : CollatzResearch.WordTrace tailWord_4091796 prefixEnd_4091796 700352696048192687677393 := by
  unfold tailWord_4091796
  simp only [CollatzResearch.WordTrace]
  refine ⟨74620030342064694982879621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99493373789419593310506161 74620030342064694982879621)
  ·
    refine ⟨13991255689137130309289929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74620030342064694982879621 13991255689137130309289929)
    ·
      refine ⟨10493441766852847731967447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13991255689137130309289929 10493441766852847731967447)
      ·
        refine ⟨15740162650279271597951171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10493441766852847731967447 15740162650279271597951171)
        ·
          refine ⟨23610243975418907396926757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15740162650279271597951171 23610243975418907396926757)
          ·
            refine ⟨4426920745391045136923767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23610243975418907396926757 4426920745391045136923767)
            ·
              refine ⟨6640381118086567705385651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426920745391045136923767 6640381118086567705385651)
              ·
                refine ⟨9960571677129851558078477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640381118086567705385651 9960571677129851558078477)
                ·
                  refine ⟨3735214378923694334279429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9960571677129851558078477 3735214378923694334279429)
                  ·
                    refine ⟨700352696048192687677393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3735214378923694334279429 700352696048192687677393)
                    ·
                      rfl

theorem cell23_4091796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_4091796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091796 prefixEnd_4091796 := by exact prefixLift 4091796
  have htrace : WordTrace (prefixWord ++ tailWord_4091796) baseStart_4091796 baseEnd_4091796 := by
    simpa [prefixWord, tailWord_4091796, baseEnd_4091796] using wordTrace_append hprefix tailTrace_4091796
  have hstable : (prefixWord ++ tailWord_4091796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091796).length < 2 ^ (prefixWord ++ tailWord_4091796).sum := by decide
  have hdescent : baseEnd_4091796 < baseStart_4091796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091809 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 6]
def baseStart_4091809 : Nat := 118140960795 + 4091809 * 2 ^ 59
def prefixEnd_4091809 : Nat := 4983230072969 + 3 ^ 40 * 4091809 * 2
def baseEnd_4091809 : Nat := 233451640377009612463291

theorem tailTrace_4091809 : CollatzResearch.WordTrace tailWord_4091809 prefixEnd_4091809 233451640377009612463291 := by
  unfold tailWord_4091809
  simp only [CollatzResearch.WordTrace]
  refine ⟨149240534833082293185982481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99493689888721528790654987 149240534833082293185982481)
  ·
    refine ⟨111930401124811719889486861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149240534833082293185982481 111930401124811719889486861)
    ·
      refine ⟨41973900421804394958557573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111930401124811719889486861 41973900421804394958557573)
      ·
        refine ⟨7870106329088324054729545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41973900421804394958557573 7870106329088324054729545)
        ·
          refine ⟨5902579746816243041047159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7870106329088324054729545 5902579746816243041047159)
          ·
            refine ⟨8853869620224364561570739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5902579746816243041047159 8853869620224364561570739)
            ·
              refine ⟨13280804430336546842356109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8853869620224364561570739 13280804430336546842356109)
              ·
                refine ⟨4980301661376205065883541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13280804430336546842356109 4980301661376205065883541)
                ·
                  refine ⟨233451640377009612463291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4980301661376205065883541 233451640377009612463291)
                  ·
                    rfl

theorem cell23_4091809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 6].length) (baseStart_4091809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091809 prefixEnd_4091809 := by exact prefixLift 4091809
  have htrace : WordTrace (prefixWord ++ tailWord_4091809) baseStart_4091809 baseEnd_4091809 := by
    simpa [prefixWord, tailWord_4091809, baseEnd_4091809] using wordTrace_append hprefix tailTrace_4091809
  have hstable : (prefixWord ++ tailWord_4091809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091809).length < 2 ^ (prefixWord ++ tailWord_4091809).sum := by decide
  have hdescent : baseEnd_4091809 < baseStart_4091809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091835 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 3, 6]
def baseStart_4091835 : Nat := 118140960795 + 4091835 * 2 ^ 59
def prefixEnd_4091835 : Nat := 4983230072969 + 3 ^ 40 * 4091835 * 2
def baseEnd_4091835 : Nat := 700359371296701136814833

theorem tailTrace_4091835 : CollatzResearch.WordTrace tailWord_4091835 prefixEnd_4091835 700359371296701136814833 := by
  unfold tailWord_4091835
  simp only [CollatzResearch.WordTrace]
  refine ⟨149241483130988099626428959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99494322087325399750952639 149241483130988099626428959)
  ·
    refine ⟨223862224696482149439643439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149241483130988099626428959 223862224696482149439643439)
    ·
      refine ⟨335793337044723224159465159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223862224696482149439643439 335793337044723224159465159)
      ·
        refine ⟨503690005567084836239197739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335793337044723224159465159 503690005567084836239197739)
        ·
          refine ⟨755535008350627254358796609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503690005567084836239197739 755535008350627254358796609)
          ·
            refine ⟨566651256262970440769097457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755535008350627254358796609 566651256262970440769097457)
            ·
              refine ⟨424988442197227830576823093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566651256262970440769097457 424988442197227830576823093)
              ·
                refine ⟨39842666455990109116577165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424988442197227830576823093 39842666455990109116577165)
                ·
                  refine ⟨14940999920996290918716437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39842666455990109116577165 14940999920996290918716437)
                  ·
                    refine ⟨700359371296701136814833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14940999920996290918716437 700359371296701136814833)
                    ·
                      rfl

theorem cell23_4091835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 6].length) (baseStart_4091835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091835 prefixEnd_4091835 := by exact prefixLift 4091835
  have htrace : WordTrace (prefixWord ++ tailWord_4091835) baseStart_4091835 baseEnd_4091835 := by
    simpa [prefixWord, tailWord_4091835, baseEnd_4091835] using wordTrace_append hprefix tailTrace_4091835
  have hstable : (prefixWord ++ tailWord_4091835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091835).length < 2 ^ (prefixWord ++ tailWord_4091835).sum := by decide
  have hdescent : baseEnd_4091835 < baseStart_4091835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091839 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 1, 5]
def baseStart_4091839 : Nat := 118140960795 + 4091839 * 2 ^ 59
def prefixEnd_4091839 : Nat := 4983230072969 + 3 ^ 40 * 4091839 * 2
def baseEnd_4091839 : Nat := 700360055937573798264827

theorem tailTrace_4091839 : CollatzResearch.WordTrace tailWord_4091839 prefixEnd_4091839 700360055937573798264827 := by
  unfold tailWord_4091839
  simp only [CollatzResearch.WordTrace]
  refine ⟨149241629022973608309574571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99494419348649072206383047 149241629022973608309574571)
  ·
    refine ⟨223862443534460412464361857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149241629022973608309574571 223862443534460412464361857)
    ·
      refine ⟨167896832650845309348271393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223862443534460412464361857 167896832650845309348271393)
      ·
        refine ⟨125922624488133982011203545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167896832650845309348271393 125922624488133982011203545)
        ·
          refine ⟨94441968366100486508402659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125922624488133982011203545 94441968366100486508402659)
          ·
            refine ⟨141662952549150729762603989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94441968366100486508402659 141662952549150729762603989)
            ·
              refine ⟨3320225450370720228811031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 141662952549150729762603989 3320225450370720228811031)
              ·
                refine ⟨4980338175556080343216547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320225450370720228811031 4980338175556080343216547)
                ·
                  refine ⟨7470507263334120514824821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980338175556080343216547 7470507263334120514824821)
                  ·
                    refine ⟨700360055937573798264827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7470507263334120514824821 700360055937573798264827)
                    ·
                      rfl

theorem cell23_4091839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 5].length) (baseStart_4091839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091839 prefixEnd_4091839 := by exact prefixLift 4091839
  have htrace : WordTrace (prefixWord ++ tailWord_4091839) baseStart_4091839 baseEnd_4091839 := by
    simpa [prefixWord, tailWord_4091839, baseEnd_4091839] using wordTrace_append hprefix tailTrace_4091839
  have hstable : (prefixWord ++ tailWord_4091839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091839).length < 2 ^ (prefixWord ++ tailWord_4091839).sum := by decide
  have hdescent : baseEnd_4091839 < baseStart_4091839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091876 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 3, 2, 2]
def baseStart_4091876 : Nat := 118140960795 + 4091876 * 2 ^ 59
def prefixEnd_4091876 : Nat := 4983230072969 + 3 ^ 40 * 4091876 * 2
def baseEnd_4091876 : Nat := 2101099166596937750031811

theorem tailTrace_4091876 : CollatzResearch.WordTrace tailWord_4091876 prefixEnd_4091876 2101099166596937750031811 := by
  unfold tailWord_4091876
  simp only [CollatzResearch.WordTrace]
  refine ⟨74621489261919781814335741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99495319015893042419114321 74621489261919781814335741)
  ·
    refine ⟨27983058473219918180375903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74621489261919781814335741 27983058473219918180375903)
    ·
      refine ⟨41974587709829877270563855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27983058473219918180375903 41974587709829877270563855)
      ·
        refine ⟨62961881564744815905845783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41974587709829877270563855 62961881564744815905845783)
        ·
          refine ⟨94442822347117223858768675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62961881564744815905845783 94442822347117223858768675)
          ·
            refine ⟨141664233520675835788153013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94442822347117223858768675 141664233520675835788153013)
            ·
              refine ⟨13281021892563359605139345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141664233520675835788153013 13281021892563359605139345)
              ·
                refine ⟨9960766419422519703854509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13281021892563359605139345 9960766419422519703854509)
                ·
                  refine ⟨3735287407283444888945441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9960766419422519703854509 3735287407283444888945441)
                  ·
                    refine ⟨2801465555462583666709081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3735287407283444888945441 2801465555462583666709081)
                    ·
                      refine ⟨2101099166596937750031811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801465555462583666709081 2101099166596937750031811)
                      ·
                        rfl

theorem cell23_4091876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_4091876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091876 prefixEnd_4091876 := by exact prefixLift 4091876
  have htrace : WordTrace (prefixWord ++ tailWord_4091876) baseStart_4091876 baseEnd_4091876 := by
    simpa [prefixWord, tailWord_4091876, baseEnd_4091876] using wordTrace_append hprefix tailTrace_4091876
  have hstable : (prefixWord ++ tailWord_4091876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091876).length < 2 ^ (prefixWord ++ tailWord_4091876).sum := by decide
  have hdescent : baseEnd_4091876 < baseStart_4091876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091896 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 1, 2, 3]
def baseStart_4091896 : Nat := 118140960795 + 4091896 * 2 ^ 59
def prefixEnd_4091896 : Nat := 4983230072969 + 3 ^ 40 * 4091896 * 2
def baseEnd_4091896 : Nat := 2101109436210027671781719

theorem tailTrace_4091896 : CollatzResearch.WordTrace tailWord_4091896 prefixEnd_4091896 2101109436210027671781719 := by
  unfold tailWord_4091896
  simp only [CollatzResearch.WordTrace]
  refine ⟨74621853991883553522199771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99495805322511404696266361 74621853991883553522199771)
  ·
    refine ⟨111932780987825330283299657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74621853991883553522199771 111932780987825330283299657)
    ·
      refine ⟨83949585740868997712474743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111932780987825330283299657 83949585740868997712474743)
      ·
        refine ⟨125924378611303496568712115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83949585740868997712474743 125924378611303496568712115)
        ·
          refine ⟨188886567916955244853068173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125924378611303496568712115 188886567916955244853068173)
          ·
            refine ⟨70832462968858216819900565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188886567916955244853068173 70832462968858216819900565)
            ·
              refine ⟨3320271701665228913432839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70832462968858216819900565 3320271701665228913432839)
              ·
                refine ⟨4980407552497843370149259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320271701665228913432839 4980407552497843370149259)
                ·
                  refine ⟨7470611328746765055223889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980407552497843370149259 7470611328746765055223889)
                  ·
                    refine ⟨5602958496560073791417917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7470611328746765055223889 5602958496560073791417917)
                    ·
                      refine ⟨2101109436210027671781719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5602958496560073791417917 2101109436210027671781719)
                      ·
                        rfl

theorem cell23_4091896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 2, 3].length) (baseStart_4091896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091896 prefixEnd_4091896 := by exact prefixLift 4091896
  have htrace : WordTrace (prefixWord ++ tailWord_4091896) baseStart_4091896 baseEnd_4091896 := by
    simpa [prefixWord, tailWord_4091896, baseEnd_4091896] using wordTrace_append hprefix tailTrace_4091896
  have hstable : (prefixWord ++ tailWord_4091896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091896).length < 2 ^ (prefixWord ++ tailWord_4091896).sum := by decide
  have hdescent : baseEnd_4091896 < baseStart_4091896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091944 : List Nat := [2, 1, 5, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4091944 : Nat := 118140960795 + 4091944 * 2 ^ 59
def prefixEnd_4091944 : Nat := 4983230072969 + 3 ^ 40 * 4091944 * 2
def baseEnd_4091944 : Nat := 2101134083281443483981499

theorem tailTrace_4091944 : CollatzResearch.WordTrace tailWord_4091944 prefixEnd_4091944 2101134083281443483981499 := by
  unfold tailWord_4091944
  simp only [CollatzResearch.WordTrace]
  refine ⟨74622729343796605621073443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99496972458395474161431257 74622729343796605621073443)
  ·
    refine ⟨111934094015694908431610165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74622729343796605621073443 111934094015694908431610165)
    ·
      refine ⟨10493821313971397665463453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111934094015694908431610165 10493821313971397665463453)
      ·
        refine ⟨3935182992739274124548795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10493821313971397665463453 3935182992739274124548795)
        ·
          refine ⟨5902774489108911186823193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935182992739274124548795 5902774489108911186823193)
          ·
            refine ⟨4427080866831683390117395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5902774489108911186823193 4427080866831683390117395)
            ·
              refine ⟨6640621300247525085176093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427080866831683390117395 6640621300247525085176093)
              ·
                refine ⟨2490232987592821906941035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6640621300247525085176093 2490232987592821906941035)
                ·
                  refine ⟨3735349481389232860411553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490232987592821906941035 3735349481389232860411553)
                  ·
                    refine ⟨2801512111041924645308665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3735349481389232860411553 2801512111041924645308665)
                    ·
                      refine ⟨2101134083281443483981499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801512111041924645308665 2101134083281443483981499)
                      ·
                        rfl

theorem cell23_4091944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4091944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091944 prefixEnd_4091944 := by exact prefixLift 4091944
  have htrace : WordTrace (prefixWord ++ tailWord_4091944) baseStart_4091944 baseEnd_4091944 := by
    simpa [prefixWord, tailWord_4091944, baseEnd_4091944] using wordTrace_append hprefix tailTrace_4091944
  have hstable : (prefixWord ++ tailWord_4091944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091944).length < 2 ^ (prefixWord ++ tailWord_4091944).sum := by decide
  have hdescent : baseEnd_4091944 < baseStart_4091944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4091952 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 5]
def baseStart_4091952 : Nat := 118140960795 + 4091952 * 2 ^ 59
def prefixEnd_4091952 : Nat := 4983230072969 + 3 ^ 40 * 4091952 * 2
def baseEnd_4091952 : Nat := 2101138191126679452681461

theorem tailTrace_4091952 : CollatzResearch.WordTrace tailWord_4091952 prefixEnd_4091952 2101138191126679452681461 := by
  unfold tailWord_4091952
  simp only [CollatzResearch.WordTrace]
  refine ⟨74622875235782114304219055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99497166981042819072292073 74622875235782114304219055)
  ·
    refine ⟨111934312853673171456328583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74622875235782114304219055 111934312853673171456328583)
    ·
      refine ⟨167901469280509757184492875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111934312853673171456328583 167901469280509757184492875)
      ·
        refine ⟨251852203920764635776739313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167901469280509757184492875 251852203920764635776739313)
        ·
          refine ⟨188889152940573476832554485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251852203920764635776739313 188889152940573476832554485)
          ·
            refine ⟨17708358088178763453051983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188889152940573476832554485 17708358088178763453051983)
            ·
              refine ⟨26562537132268145179577975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17708358088178763453051983 26562537132268145179577975)
              ·
                refine ⟨39843805698402217769366963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26562537132268145179577975 39843805698402217769366963)
                ·
                  refine ⟨59765708547603326654050445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39843805698402217769366963 59765708547603326654050445)
                  ·
                    refine ⟨22412140705351247495268917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59765708547603326654050445 22412140705351247495268917)
                    ·
                      refine ⟨2101138191126679452681461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22412140705351247495268917 2101138191126679452681461)
                      ·
                        rfl

theorem cell23_4091952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_4091952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4091952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4091952 prefixEnd_4091952 := by exact prefixLift 4091952
  have htrace : WordTrace (prefixWord ++ tailWord_4091952) baseStart_4091952 baseEnd_4091952 := by
    simpa [prefixWord, tailWord_4091952, baseEnd_4091952] using wordTrace_append hprefix tailTrace_4091952
  have hstable : (prefixWord ++ tailWord_4091952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4091952).length < 2 ^ (prefixWord ++ tailWord_4091952).sum := by decide
  have hdescent : baseEnd_4091952 < baseStart_4091952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4091952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092023 : List Nat := [1, 1, 3, 1, 1, 7, 2, 2, 5]
def baseStart_4092023 : Nat := 118140960795 + 4092023 * 2 ^ 59
def prefixEnd_4092023 : Nat := 4983230072969 + 3 ^ 40 * 4092023 * 2
def baseEnd_4092023 : Nat := 233463849805905408321515

theorem tailTrace_4092023 : CollatzResearch.WordTrace tailWord_4092023 prefixEnd_4092023 233463849805905408321515 := by
  unfold tailWord_4092023
  simp only [CollatzResearch.WordTrace]
  refine ⟨149248340054307007734272723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99498893369538005156181815 149248340054307007734272723)
  ·
    refine ⟨223872510081460511601409085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149248340054307007734272723 223872510081460511601409085)
    ·
      refine ⟨83952191280547691850528407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223872510081460511601409085 83952191280547691850528407)
      ·
        refine ⟨125928286920821537775792611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83952191280547691850528407 125928286920821537775792611)
        ·
          refine ⟨188892430381232306663688917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125928286920821537775792611 188892430381232306663688917)
          ·
            refine ⟨4427166337060132187430209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 188892430381232306663688917 4427166337060132187430209)
            ·
              refine ⟨3320374752795099140572657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4427166337060132187430209 3320374752795099140572657)
              ·
                refine ⟨2490281064596324355429493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3320374752795099140572657 2490281064596324355429493)
                ·
                  refine ⟨233463849805905408321515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2490281064596324355429493 233463849805905408321515)
                  ·
                    rfl

theorem cell23_4092023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 5].length) (baseStart_4092023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092023 prefixEnd_4092023 := by exact prefixLift 4092023
  have htrace : WordTrace (prefixWord ++ tailWord_4092023) baseStart_4092023 baseEnd_4092023 := by
    simpa [prefixWord, tailWord_4092023, baseEnd_4092023] using wordTrace_append hprefix tailTrace_4092023
  have hstable : (prefixWord ++ tailWord_4092023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092023).length < 2 ^ (prefixWord ++ tailWord_4092023).sum := by decide
  have hdescent : baseEnd_4092023 < baseStart_4092023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092029 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_4092029 : Nat := 118140960795 + 4092029 * 2 ^ 59
def prefixEnd_4092029 : Nat := 4983230072969 + 3 ^ 40 * 4092029 * 2
def baseEnd_4092029 : Nat := 2101177729137075651418607

theorem tailTrace_4092029 : CollatzResearch.WordTrace tailWord_4092029 prefixEnd_4092029 2101177729137075651418607 := by
  unfold tailWord_4092029
  simp only [CollatzResearch.WordTrace]
  refine ⟨149248558892285270758991141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99499039261523513839327427 149248558892285270758991141)
  ·
    refine ⟨27984104792303488267310839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149248558892285270758991141 27984104792303488267310839)
    ·
      refine ⟨41976157188455232400966259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27984104792303488267310839 41976157188455232400966259)
      ·
        refine ⟨62964235782682848601449389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41976157188455232400966259 62964235782682848601449389)
        ·
          refine ⟨23611588418506068225543521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62964235782682848601449389 23611588418506068225543521)
          ·
            refine ⟨17708691313879551169157641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23611588418506068225543521 17708691313879551169157641)
            ·
              refine ⟨13281518485409663376868231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17708691313879551169157641 13281518485409663376868231)
              ·
                refine ⟨19922277728114495065302347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13281518485409663376868231 19922277728114495065302347)
                ·
                  refine ⟨29883416592171742597953521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19922277728114495065302347 29883416592171742597953521)
                  ·
                    refine ⟨22412562444128806948465141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29883416592171742597953521 22412562444128806948465141)
                    ·
                      refine ⟨2101177729137075651418607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22412562444128806948465141 2101177729137075651418607)
                      ·
                        rfl

theorem cell23_4092029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_4092029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092029 prefixEnd_4092029 := by exact prefixLift 4092029
  have htrace : WordTrace (prefixWord ++ tailWord_4092029) baseStart_4092029 baseEnd_4092029 := by
    simpa [prefixWord, tailWord_4092029, baseEnd_4092029] using wordTrace_append hprefix tailTrace_4092029
  have hstable : (prefixWord ++ tailWord_4092029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092029).length < 2 ^ (prefixWord ++ tailWord_4092029).sum := by decide
  have hdescent : baseEnd_4092029 < baseStart_4092029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092032 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 2, 8]
def baseStart_4092032 : Nat := 118140960795 + 4092032 * 2 ^ 59
def prefixEnd_4092032 : Nat := 4983230072969 + 3 ^ 40 * 4092032 * 2
def baseEnd_4092032 : Nat := 700393089859679713227031

theorem tailTrace_4092032 : CollatzResearch.WordTrace tailWord_4092032 prefixEnd_4092032 700393089859679713227031 := by
  unfold tailWord_4092032
  simp only [CollatzResearch.WordTrace]
  refine ⟨74624334155637201135675175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99499112207516268180900233 74624334155637201135675175)
  ·
    refine ⟨111936501233455801703512763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74624334155637201135675175 111936501233455801703512763)
    ·
      refine ⟨167904751850183702555269145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111936501233455801703512763 167904751850183702555269145)
      ·
        refine ⟨125928563887637776916451859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167904751850183702555269145 125928563887637776916451859)
        ·
          refine ⟨188892845831456665374677789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125928563887637776916451859 188892845831456665374677789)
          ·
            refine ⟨70834817186796249515504171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188892845831456665374677789 70834817186796249515504171)
            ·
              refine ⟨106252225780194374273256257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70834817186796249515504171 106252225780194374273256257)
              ·
                refine ⟨79689169335145780704942193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106252225780194374273256257 79689169335145780704942193)
                ·
                  refine ⟨59766877001359335528706645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79689169335145780704942193 59766877001359335528706645)
                  ·
                    refine ⟨700393089859679713227031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59766877001359335528706645 700393089859679713227031)
                    ·
                      rfl

theorem cell23_4092032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_4092032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092032 prefixEnd_4092032 := by exact prefixLift 4092032
  have htrace : WordTrace (prefixWord ++ tailWord_4092032) baseStart_4092032 baseEnd_4092032 := by
    simpa [prefixWord, tailWord_4092032, baseEnd_4092032] using wordTrace_append hprefix tailTrace_4092032
  have hstable : (prefixWord ++ tailWord_4092032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092032).length < 2 ^ (prefixWord ++ tailWord_4092032).sum := by decide
  have hdescent : baseEnd_4092032 < baseStart_4092032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092039 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_4092039 : Nat := 118140960795 + 4092039 * 2 ^ 59
def prefixEnd_4092039 : Nat := 4983230072969 + 3 ^ 40 * 4092039 * 2
def baseEnd_4092039 : Nat := 2101182863943620612293561

theorem tailTrace_4092039 : CollatzResearch.WordTrace tailWord_4092039 prefixEnd_4092039 2101182863943620612293561 := by
  unfold tailWord_4092039
  simp only [CollatzResearch.WordTrace]
  refine ⟨149248923622249042466855171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99499282414832694977903447 149248923622249042466855171)
  ·
    refine ⟨223873385433373563700282757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149248923622249042466855171 223873385433373563700282757)
    ·
      refine ⟨41976259768757543193803017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223873385433373563700282757 41976259768757543193803017)
      ·
        refine ⟨31482194826568157395352263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41976259768757543193803017 31482194826568157395352263)
        ·
          refine ⟨47223292239852236093028395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31482194826568157395352263 47223292239852236093028395)
          ·
            refine ⟨70834938359778354139542593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47223292239852236093028395 70834938359778354139542593)
            ·
              refine ⟨53126203769833765604656945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70834938359778354139542593 53126203769833765604656945)
              ·
                refine ⟨39844652827375324203492709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53126203769833765604656945 39844652827375324203492709)
                ·
                  refine ⟨7470872405132873288154883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39844652827375324203492709 7470872405132873288154883)
                  ·
                    refine ⟨11206308607699309932232325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7470872405132873288154883 11206308607699309932232325)
                    ·
                      refine ⟨2101182863943620612293561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11206308607699309932232325 2101182863943620612293561)
                      ·
                        rfl

theorem cell23_4092039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_4092039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092039 prefixEnd_4092039 := by exact prefixLift 4092039
  have htrace : WordTrace (prefixWord ++ tailWord_4092039) baseStart_4092039 baseEnd_4092039 := by
    simpa [prefixWord, tailWord_4092039, baseEnd_4092039] using wordTrace_append hprefix tailTrace_4092039
  have hstable : (prefixWord ++ tailWord_4092039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092039).length < 2 ^ (prefixWord ++ tailWord_4092039).sum := by decide
  have hdescent : baseEnd_4092039 < baseStart_4092039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092056 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 1, 3, 4]
def baseStart_4092056 : Nat := 118140960795 + 4092056 * 2 ^ 59
def prefixEnd_4092056 : Nat := 4983230072969 + 3 ^ 40 * 4092056 * 2
def baseEnd_4092056 : Nat := 2101191593114747045780983

theorem tailTrace_4092056 : CollatzResearch.WordTrace tailWord_4092056 prefixEnd_4092056 2101191593114747045780983 := by
  unfold tailWord_4092056
  simp only [CollatzResearch.WordTrace]
  refine ⟨74624771831593727185112011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99499695775458302913482681 74624771831593727185112011)
  ·
    refine ⟨111937157747390590777668017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74624771831593727185112011 111937157747390590777668017)
    ·
      refine ⟨83952868310542943083251013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111937157747390590777668017 83952868310542943083251013)
      ·
        refine ⟨15741162808226801828109565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83952868310542943083251013 15741162808226801828109565)
        ·
          refine ⟨5902936053085050685541087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15741162808226801828109565 5902936053085050685541087)
          ·
            refine ⟨8854404079627576028311631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5902936053085050685541087 8854404079627576028311631)
            ·
              refine ⟨13281606119441364042467447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8854404079627576028311631 13281606119441364042467447)
              ·
                refine ⟨19922409179162046063701171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13281606119441364042467447 19922409179162046063701171)
                ·
                  refine ⟨29883613768743069095551757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19922409179162046063701171 29883613768743069095551757)
                  ·
                    refine ⟨11206355163278650910831909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29883613768743069095551757 11206355163278650910831909)
                    ·
                      refine ⟨2101191593114747045780983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11206355163278650910831909 2101191593114747045780983)
                      ·
                        rfl

theorem cell23_4092056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_4092056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092056 prefixEnd_4092056 := by exact prefixLift 4092056
  have htrace : WordTrace (prefixWord ++ tailWord_4092056) baseStart_4092056 baseEnd_4092056 := by
    simpa [prefixWord, tailWord_4092056, baseEnd_4092056] using wordTrace_append hprefix tailTrace_4092056
  have hstable : (prefixWord ++ tailWord_4092056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092056).length < 2 ^ (prefixWord ++ tailWord_4092056).sum := by decide
  have hdescent : baseEnd_4092056 < baseStart_4092056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092059 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 3]
def baseStart_4092059 : Nat := 118140960795 + 4092059 * 2 ^ 59
def prefixEnd_4092059 : Nat := 4983230072969 + 3 ^ 40 * 4092059 * 2
def baseEnd_4092059 : Nat := 2101193133556710534043469

theorem tailTrace_4092059 : CollatzResearch.WordTrace tailWord_4092059 prefixEnd_4092059 2101193133556710534043469 := by
  unfold tailWord_4092059
  simp only [CollatzResearch.WordTrace]
  refine ⟨149249653082176585882583231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99499768721451057255055487 149249653082176585882583231)
  ·
    refine ⟨223874479623264878823874847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149249653082176585882583231 223874479623264878823874847)
    ·
      refine ⟨335811719434897318235812271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223874479623264878823874847 335811719434897318235812271)
      ·
        refine ⟨503717579152345977353718407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335811719434897318235812271 503717579152345977353718407)
        ·
          refine ⟨755576368728518966030577611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503717579152345977353718407 755576368728518966030577611)
          ·
            refine ⟨1133364553092778449045866417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755576368728518966030577611 1133364553092778449045866417)
            ·
              refine ⟨850023414819583836784399813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133364553092778449045866417 850023414819583836784399813)
              ·
                refine ⟨159379390278671969397074965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 850023414819583836784399813 159379390278671969397074965)
                ·
                  refine ⟨7470908919312748565487889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159379390278671969397074965 7470908919312748565487889)
                  ·
                    refine ⟨5603181689484561424115917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7470908919312748565487889 5603181689484561424115917)
                    ·
                      refine ⟨2101193133556710534043469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5603181689484561424115917 2101193133556710534043469)
                      ·
                        rfl

theorem cell23_4092059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 3].length) (baseStart_4092059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092059 prefixEnd_4092059 := by exact prefixLift 4092059
  have htrace : WordTrace (prefixWord ++ tailWord_4092059) baseStart_4092059 baseEnd_4092059 := by
    simpa [prefixWord, tailWord_4092059, baseEnd_4092059] using wordTrace_append hprefix tailTrace_4092059
  have hstable : (prefixWord ++ tailWord_4092059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092059).length < 2 ^ (prefixWord ++ tailWord_4092059).sum := by decide
  have hdescent : baseEnd_4092059 < baseStart_4092059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092117 : List Nat := [1, 3, 2, 4, 2, 2, 1, 3, 1, 4]
def baseStart_4092117 : Nat := 118140960795 + 4092117 * 2 ^ 59
def prefixEnd_4092117 : Nat := 4983230072969 + 3 ^ 40 * 4092117 * 2
def baseEnd_4092117 : Nat := 700407638478223769039401

theorem tailTrace_4092117 : CollatzResearch.WordTrace tailWord_4092117 prefixEnd_4092117 700407638478223769039401 := by
  unfold tailWord_4092117
  simp only [CollatzResearch.WordTrace]
  refine ⟨149251768515966461788194605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99501179010644307858796403 149251768515966461788194605)
  ·
    refine ⟨55969413193487423170572977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149251768515966461788194605 55969413193487423170572977)
    ·
      refine ⟨41977059895115567377929733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55969413193487423170572977 41977059895115567377929733)
      ·
        refine ⟨7870698730334168883361825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41977059895115567377929733 7870698730334168883361825)
        ·
          refine ⟨5903024047750626662521369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7870698730334168883361825 5903024047750626662521369)
          ·
            refine ⟨4427268035812969996891027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5903024047750626662521369 4427268035812969996891027)
            ·
              refine ⟨6640902053719454995336541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427268035812969996891027 6640902053719454995336541)
              ·
                refine ⟨2490338270144795623251203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6640902053719454995336541 2490338270144795623251203)
                ·
                  refine ⟨3735507405217193434876805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490338270144795623251203 3735507405217193434876805)
                  ·
                    refine ⟨700407638478223769039401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3735507405217193434876805 700407638478223769039401)
                    ·
                      rfl

theorem cell23_4092117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_4092117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092117 prefixEnd_4092117 := by exact prefixLift 4092117
  have htrace : WordTrace (prefixWord ++ tailWord_4092117) baseStart_4092117 baseEnd_4092117 := by
    simpa [prefixWord, tailWord_4092117, baseEnd_4092117] using wordTrace_append hprefix tailTrace_4092117
  have hstable : (prefixWord ++ tailWord_4092117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092117).length < 2 ^ (prefixWord ++ tailWord_4092117).sum := by decide
  have hdescent : baseEnd_4092117 < baseStart_4092117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092133 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 4, 3, 2]
def baseStart_4092133 : Nat := 118140960795 + 4092133 * 2 ^ 59
def prefixEnd_4092133 : Nat := 4983230072969 + 3 ^ 40 * 4092133 * 2
def baseEnd_4092133 : Nat := 2101231131125143244518129

theorem tailTrace_4092133 : CollatzResearch.WordTrace tailWord_4092133 prefixEnd_4092133 2101231131125143244518129 := by
  unfold tailWord_4092133
  simp only [CollatzResearch.WordTrace]
  refine ⟨149252352083908496520777053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99501568055938997680518035 149252352083908496520777053)
  ·
    refine ⟨55969632031465686195291395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149252352083908496520777053 55969632031465686195291395)
    ·
      refine ⟨83954448047198529292937093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55969632031465686195291395 83954448047198529292937093)
      ·
        refine ⟨15741459008849724242425705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83954448047198529292937093 15741459008849724242425705)
        ·
          refine ⟨11806094256637293181819279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15741459008849724242425705 11806094256637293181819279)
          ·
            refine ⟨17709141384955939772728919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11806094256637293181819279 17709141384955939772728919)
            ·
              refine ⟨26563712077433909659093379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17709141384955939772728919 26563712077433909659093379)
              ·
                refine ⟨39845568116150864488640069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26563712077433909659093379 39845568116150864488640069)
                ·
                  refine ⟨7471044021778287091620013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39845568116150864488640069 7471044021778287091620013)
                  ·
                    refine ⟨2801641508166857659357505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7471044021778287091620013 2801641508166857659357505)
                    ·
                      refine ⟨2101231131125143244518129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801641508166857659357505 2101231131125143244518129)
                      ·
                        rfl

theorem cell23_4092133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_4092133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092133 prefixEnd_4092133 := by exact prefixLift 4092133
  have htrace : WordTrace (prefixWord ++ tailWord_4092133) baseStart_4092133 baseEnd_4092133 := by
    simpa [prefixWord, tailWord_4092133, baseEnd_4092133] using wordTrace_append hprefix tailTrace_4092133
  have hstable : (prefixWord ++ tailWord_4092133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092133).length < 2 ^ (prefixWord ++ tailWord_4092133).sum := by decide
  have hdescent : baseEnd_4092133 < baseStart_4092133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092159 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 6]
def baseStart_4092159 : Nat := 118140960795 + 4092159 * 2 ^ 59
def prefixEnd_4092159 : Nat := 4983230072969 + 3 ^ 40 * 4092159 * 2
def baseEnd_4092159 : Nat := 2101244481622160142793009

theorem tailTrace_4092159 : CollatzResearch.WordTrace tailWord_4092159 prefixEnd_4092159 2101244481622160142793009 := by
  unfold tailWord_4092159
  simp only [CollatzResearch.WordTrace]
  refine ⟨149253300381814302961223531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99502200254542868640815687 149253300381814302961223531)
  ·
    refine ⟨223879950572721454441835297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149253300381814302961223531 223879950572721454441835297)
    ·
      refine ⟨167909962929541090831376473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223879950572721454441835297 167909962929541090831376473)
      ·
        refine ⟨125932472197155818123532355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167909962929541090831376473 125932472197155818123532355)
        ·
          refine ⟨188898708295733727185298533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125932472197155818123532355 188898708295733727185298533)
          ·
            refine ⟨35418507805450073847243475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188898708295733727185298533 35418507805450073847243475)
            ·
              refine ⟨53127761708175110770865213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35418507805450073847243475 53127761708175110770865213)
              ·
                refine ⟨19922910640565666539074455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53127761708175110770865213 19922910640565666539074455)
                ·
                  refine ⟨29884365960848499808611683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19922910640565666539074455 29884365960848499808611683)
                  ·
                    refine ⟨44826548941272749712917525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29884365960848499808611683 44826548941272749712917525)
                    ·
                      refine ⟨2101244481622160142793009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44826548941272749712917525 2101244481622160142793009)
                      ·
                        rfl

theorem cell23_4092159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_4092159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092159 prefixEnd_4092159 := by exact prefixLift 4092159
  have htrace : WordTrace (prefixWord ++ tailWord_4092159) baseStart_4092159 baseEnd_4092159 := by
    simpa [prefixWord, tailWord_4092159, baseEnd_4092159] using wordTrace_append hprefix tailTrace_4092159
  have hstable : (prefixWord ++ tailWord_4092159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092159).length < 2 ^ (prefixWord ++ tailWord_4092159).sum := by decide
  have hdescent : baseEnd_4092159 < baseStart_4092159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092163 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 5, 2, 2]
def baseStart_4092163 : Nat := 118140960795 + 4092163 * 2 ^ 59
def prefixEnd_4092163 : Nat := 4983230072969 + 3 ^ 40 * 4092163 * 2
def baseEnd_4092163 : Nat := 2101246535544778127142991

theorem tailTrace_4092163 : CollatzResearch.WordTrace tailWord_4092163 prefixEnd_4092163 2101246535544778127142991 := by
  unfold tailWord_4092163
  simp only [CollatzResearch.WordTrace]
  refine ⟨149253446273799811644369143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99502297515866541096246095 149253446273799811644369143)
  ·
    refine ⟨223880169410699717466553715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149253446273799811644369143 223880169410699717466553715)
    ·
      refine ⟨335820254116049576199830573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223880169410699717466553715 335820254116049576199830573)
      ·
        refine ⟨125932595293518591074936465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335820254116049576199830573 125932595293518591074936465)
        ·
          refine ⟨94449446470138943306202349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125932595293518591074936465 94449446470138943306202349)
          ·
            refine ⟨35418542426302103739825881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94449446470138943306202349 35418542426302103739825881)
            ·
              refine ⟨26563906819726577804869411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35418542426302103739825881 26563906819726577804869411)
              ·
                refine ⟨39845860229589866707304117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26563906819726577804869411 39845860229589866707304117)
                ·
                  refine ⟨3735549396524050003809761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39845860229589866707304117 3735549396524050003809761)
                  ·
                    refine ⟨2801662047393037502857321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3735549396524050003809761 2801662047393037502857321)
                    ·
                      refine ⟨2101246535544778127142991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801662047393037502857321 2101246535544778127142991)
                      ·
                        rfl

theorem cell23_4092163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 2, 2].length) (baseStart_4092163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092163 prefixEnd_4092163 := by exact prefixLift 4092163
  have htrace : WordTrace (prefixWord ++ tailWord_4092163) baseStart_4092163 baseEnd_4092163 := by
    simpa [prefixWord, tailWord_4092163, baseEnd_4092163] using wordTrace_append hprefix tailTrace_4092163
  have hstable : (prefixWord ++ tailWord_4092163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092163).length < 2 ^ (prefixWord ++ tailWord_4092163).sum := by decide
  have hdescent : baseEnd_4092163 < baseStart_4092163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092167 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 2, 3, 2]
def baseStart_4092167 : Nat := 118140960795 + 4092167 * 2 ^ 59
def prefixEnd_4092167 : Nat := 4983230072969 + 3 ^ 40 * 4092167 * 2
def baseEnd_4092167 : Nat := 2101248589467396111492973

theorem tailTrace_4092167 : CollatzResearch.WordTrace tailWord_4092167 prefixEnd_4092167 2101248589467396111492973 := by
  unfold tailWord_4092167
  simp only [CollatzResearch.WordTrace]
  refine ⟨149253592165785320327514755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99502394777190213551676503 149253592165785320327514755)
  ·
    refine ⟨223880388248677980491272133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149253592165785320327514755 223880388248677980491272133)
    ·
      refine ⟨41977572796627121342113525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223880388248677980491272133 41977572796627121342113525)
      ·
        refine ⟨3935397449683792625823143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41977572796627121342113525 3935397449683792625823143)
        ·
          refine ⟨5903096174525688938734715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935397449683792625823143 5903096174525688938734715)
          ·
            refine ⟨8854644261788533408102073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903096174525688938734715 8854644261788533408102073)
            ·
              refine ⟨6640983196341400056076555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8854644261788533408102073 6640983196341400056076555)
              ·
                refine ⟨9961474794512100084114833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640983196341400056076555 9961474794512100084114833)
                ·
                  refine ⟨7471106095884075063086125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9961474794512100084114833 7471106095884075063086125)
                  ·
                    refine ⟨2801664785956528148657297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7471106095884075063086125 2801664785956528148657297)
                    ·
                      refine ⟨2101248589467396111492973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2801664785956528148657297 2101248589467396111492973)
                      ·
                        rfl

theorem cell23_4092167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_4092167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092167 prefixEnd_4092167 := by exact prefixLift 4092167
  have htrace : WordTrace (prefixWord ++ tailWord_4092167) baseStart_4092167 baseEnd_4092167 := by
    simpa [prefixWord, tailWord_4092167, baseEnd_4092167] using wordTrace_append hprefix tailTrace_4092167
  have hstable : (prefixWord ++ tailWord_4092167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092167).length < 2 ^ (prefixWord ++ tailWord_4092167).sum := by decide
  have hdescent : baseEnd_4092167 < baseStart_4092167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092169 : List Nat := [1, 2, 1, 1, 3, 4, 2, 9]
def baseStart_4092169 : Nat := 118140960795 + 4092169 * 2 ^ 59
def prefixEnd_4092169 : Nat := 4983230072969 + 3 ^ 40 * 4092169 * 2
def baseEnd_4092169 : Nat := 77824059867729818654369

theorem tailTrace_4092169 : CollatzResearch.WordTrace tailWord_4092169 prefixEnd_4092169 77824059867729818654369 := by
  unfold tailWord_4092169
  simp only [CollatzResearch.WordTrace]
  refine ⟨149253665111778074669087561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99502443407852049779391707 149253665111778074669087561)
  ·
    refine ⟨111940248833833556001815671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149253665111778074669087561 111940248833833556001815671)
    ·
      refine ⟨167910373250750334002723507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111940248833833556001815671 167910373250750334002723507)
      ·
        refine ⟨251865559876125501004085261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167910373250750334002723507 251865559876125501004085261)
        ·
          refine ⟨94449584953547062876531973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251865559876125501004085261 94449584953547062876531973)
          ·
            refine ⟨17709297178790074289349745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94449584953547062876531973 17709297178790074289349745)
            ·
              refine ⟨13281972884092555717012309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17709297178790074289349745 13281972884092555717012309)
              ·
                refine ⟨77824059867729818654369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13281972884092555717012309 77824059867729818654369)
                ·
                  rfl

theorem cell23_4092169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 9].length) (baseStart_4092169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092169 prefixEnd_4092169 := by exact prefixLift 4092169
  have htrace : WordTrace (prefixWord ++ tailWord_4092169) baseStart_4092169 baseEnd_4092169 := by
    simpa [prefixWord, tailWord_4092169, baseEnd_4092169] using wordTrace_append hprefix tailTrace_4092169
  have hstable : (prefixWord ++ tailWord_4092169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092169).length < 2 ^ (prefixWord ++ tailWord_4092169).sum := by decide
  have hdescent : baseEnd_4092169 < baseStart_4092169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092183 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 5]
def baseStart_4092183 : Nat := 118140960795 + 4092183 * 2 ^ 59
def prefixEnd_4092183 : Nat := 4983230072969 + 3 ^ 40 * 4092183 * 2
def baseEnd_4092183 : Nat := 2101256805157868048892899

theorem tailTrace_4092183 : CollatzResearch.WordTrace tailWord_4092183 prefixEnd_4092183 2101256805157868048892899 := by
  unfold tailWord_4092183
  simp only [CollatzResearch.WordTrace]
  refine ⟨149254175733727355060097203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99502783822484903373398135 149254175733727355060097203)
  ·
    refine ⟨223881263600591032590145805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149254175733727355060097203 223881263600591032590145805)
    ·
      refine ⟨83955473850221637221304677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223881263600591032590145805 83955473850221637221304677)
      ·
        refine ⟨15741651346916556978994627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83955473850221637221304677 15741651346916556978994627)
        ·
          refine ⟨23612477020374835468491941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15741651346916556978994627 23612477020374835468491941)
          ·
            refine ⟨4427339441320281650342239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23612477020374835468491941 4427339441320281650342239)
            ·
              refine ⟨6641009161980422475513359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427339441320281650342239 6641009161980422475513359)
              ·
                refine ⟨9961513742970633713270039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6641009161980422475513359 9961513742970633713270039)
                ·
                  refine ⟨14942270614455950569905059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9961513742970633713270039 14942270614455950569905059)
                  ·
                    refine ⟨22413405921683925854857589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14942270614455950569905059 22413405921683925854857589)
                    ·
                      refine ⟨2101256805157868048892899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22413405921683925854857589 2101256805157868048892899)
                      ·
                        rfl

theorem cell23_4092183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_4092183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092183 prefixEnd_4092183 := by exact prefixLift 4092183
  have htrace : WordTrace (prefixWord ++ tailWord_4092183) baseStart_4092183 baseEnd_4092183 := by
    simpa [prefixWord, tailWord_4092183, baseEnd_4092183] using wordTrace_append hprefix tailTrace_4092183
  have hstable : (prefixWord ++ tailWord_4092183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092183).length < 2 ^ (prefixWord ++ tailWord_4092183).sum := by decide
  have hdescent : baseEnd_4092183 < baseStart_4092183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4092186 : List Nat := [3, 1, 1, 3, 5, 10]
def baseStart_4092186 : Nat := 118140960795 + 4092186 * 2 ^ 59
def prefixEnd_4092186 : Nat := 4983230072969 + 3 ^ 40 * 4092186 * 2
def baseEnd_4092186 : Nat := 8647153685596014556195

theorem tailTrace_4092186 : CollatzResearch.WordTrace tailWord_4092186 prefixEnd_4092186 8647153685596014556195 := by
  unfold tailWord_4092186
  simp only [CollatzResearch.WordTrace]
  refine ⟨37313571288179121643114103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99502856768477657714970941 37313571288179121643114103)
  ·
    refine ⟨55970356932268682464671155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37313571288179121643114103 55970356932268682464671155)
    ·
      refine ⟨83955535398403023697006733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55970356932268682464671155 83955535398403023697006733)
      ·
        refine ⟨31483325774401133886377525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83955535398403023697006733 31483325774401133886377525)
        ·
          refine ⟨2951561791350106301847893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31483325774401133886377525 2951561791350106301847893)
          ·
            refine ⟨8647153685596014556195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2951561791350106301847893 8647153685596014556195)
            ·
              rfl

theorem cell23_4092186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 10].length) (baseStart_4092186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4092186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4092186 prefixEnd_4092186 := by exact prefixLift 4092186
  have htrace : WordTrace (prefixWord ++ tailWord_4092186) baseStart_4092186 baseEnd_4092186 := by
    simpa [prefixWord, tailWord_4092186, baseEnd_4092186] using wordTrace_append hprefix tailTrace_4092186
  have hstable : (prefixWord ++ tailWord_4092186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4092186).length < 2 ^ (prefixWord ++ tailWord_4092186).sum := by decide
  have hdescent : baseEnd_4092186 < baseStart_4092186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4092186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
