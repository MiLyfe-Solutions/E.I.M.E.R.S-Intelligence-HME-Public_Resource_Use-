import V185TrunkScan23Chunk0403

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2388981 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 6]
def baseStart_2388981 : Nat := 118140960795 + 2388981 * 2 ^ 59
def prefixEnd_2388981 : Nat := 4983230072969 + 3 ^ 40 * 2388981 * 2
def baseEnd_2388981 : Nat := 136299503050980314950087

theorem tailTrace_2388981 : CollatzResearch.WordTrace tailWord_2388981 prefixEnd_2388981 136299503050980314950087 := by
  unfold tailWord_2388981
  simp only [CollatzResearch.WordTrace]
  refine ⟨87133295358137317316934797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58088863572091544877956531 87133295358137317316934797)
  ·
    refine ⟨32674985759301493993850549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87133295358137317316934797 32674985759301493993850549)
    ·
      refine ⟨3063279914934515061923489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32674985759301493993850549 3063279914934515061923489)
      ·
        refine ⟨2297459936200886296442617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3063279914934515061923489 2297459936200886296442617)
        ·
          refine ⟨1723094952150664722331963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2297459936200886296442617 1723094952150664722331963)
          ·
            refine ⟨2584642428225997083497945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723094952150664722331963 2584642428225997083497945)
            ·
              refine ⟨1938481821169497812623459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2584642428225997083497945 1938481821169497812623459)
              ·
                refine ⟨2907722731754246718935189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938481821169497812623459 2907722731754246718935189)
                ·
                  refine ⟨136299503050980314950087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2907722731754246718935189 136299503050980314950087)
                  ·
                    rfl

theorem cell23_2388981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_2388981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388981 prefixEnd_2388981 := by exact prefixLift 2388981
  have htrace : WordTrace (prefixWord ++ tailWord_2388981) baseStart_2388981 baseEnd_2388981 := by
    simpa [prefixWord, tailWord_2388981, baseEnd_2388981] using wordTrace_append hprefix tailTrace_2388981
  have hstable : (prefixWord ++ tailWord_2388981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388981).length < 2 ^ (prefixWord ++ tailWord_2388981).sum := by decide
  have hdescent : baseEnd_2388981 < baseStart_2388981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388993 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_2388993 : Nat := 118140960795 + 2388993 * 2 ^ 59
def prefixEnd_2388993 : Nat := 4983230072969 + 3 ^ 40 * 2388993 * 2
def baseEnd_2388993 : Nat := 1226701689226676787600727

theorem tailTrace_2388993 : CollatzResearch.WordTrace tailWord_2388993 prefixEnd_2388993 1226701689226676787600727 := by
  unfold tailWord_2388993
  simp only [CollatzResearch.WordTrace]
  refine ⟨87133733034093843366371633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58089155356062562244247755 87133733034093843366371633)
  ·
    refine ⟨65350299775570382524778725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87133733034093843366371633 65350299775570382524778725)
    ·
      refine ⟨12253181207919446723396011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65350299775570382524778725 12253181207919446723396011)
      ·
        refine ⟨18379771811879170085094017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12253181207919446723396011 18379771811879170085094017)
        ·
          refine ⟨13784828858909377563820513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18379771811879170085094017 13784828858909377563820513)
          ·
            refine ⟨10338621644182033172865385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13784828858909377563820513 10338621644182033172865385)
            ·
              refine ⟨7753966233136524879649039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10338621644182033172865385 7753966233136524879649039)
              ·
                refine ⟨11630949349704787319473559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7753966233136524879649039 11630949349704787319473559)
                ·
                  refine ⟨17446424024557180979210339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11630949349704787319473559 17446424024557180979210339)
                  ·
                    refine ⟨26169636036835771468815509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17446424024557180979210339 26169636036835771468815509)
                    ·
                      refine ⟨1226701689226676787600727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26169636036835771468815509 1226701689226676787600727)
                      ·
                        rfl

theorem cell23_2388993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_2388993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388993 prefixEnd_2388993 := by exact prefixLift 2388993
  have htrace : WordTrace (prefixWord ++ tailWord_2388993) baseStart_2388993 baseEnd_2388993 := by
    simpa [prefixWord, tailWord_2388993, baseEnd_2388993] using wordTrace_append hprefix tailTrace_2388993
  have hstable : (prefixWord ++ tailWord_2388993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388993).length < 2 ^ (prefixWord ++ tailWord_2388993).sum := by decide
  have hdescent : baseEnd_2388993 < baseStart_2388993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389000 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_2389000 : Nat := 118140960795 + 2389000 * 2 ^ 59
def prefixEnd_2389000 : Nat := 4983230072969 + 3 ^ 40 * 2389000 * 2
def baseEnd_2389000 : Nat := 1226705283591258260213195

theorem tailTrace_2389000 : CollatzResearch.WordTrace tailWord_2389000 prefixEnd_2389000 1226705283591258260213195 := by
  unfold tailWord_2389000
  simp only [CollatzResearch.WordTrace]
  refine ⟨43566994172534241780938227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58089325563378989041250969 43566994172534241780938227)
  ·
    refine ⟨65350491258801362671407341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43566994172534241780938227 65350491258801362671407341)
    ·
      refine ⟨24506434222050511001777753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65350491258801362671407341 24506434222050511001777753)
      ·
        refine ⟨18379825666537883251333315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24506434222050511001777753 18379825666537883251333315)
        ·
          refine ⟨27569738499806824876999973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18379825666537883251333315 27569738499806824876999973)
          ·
            refine ⟨5169325968713779664437495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27569738499806824876999973 5169325968713779664437495)
            ·
              refine ⟨7753988953070669496656243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5169325968713779664437495 7753988953070669496656243)
              ·
                refine ⟨11630983429606004244984365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7753988953070669496656243 11630983429606004244984365)
                ·
                  refine ⟨4361618786102251591869137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11630983429606004244984365 4361618786102251591869137)
                  ·
                    refine ⟨3271214089576688693901853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4361618786102251591869137 3271214089576688693901853)
                    ·
                      refine ⟨1226705283591258260213195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3271214089576688693901853 1226705283591258260213195)
                      ·
                        rfl

theorem cell23_2389000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_2389000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389000 prefixEnd_2389000 := by exact prefixLift 2389000
  have htrace : WordTrace (prefixWord ++ tailWord_2389000) baseStart_2389000 baseEnd_2389000 := by
    simpa [prefixWord, tailWord_2389000, baseEnd_2389000] using wordTrace_append hprefix tailTrace_2389000
  have hstable : (prefixWord ++ tailWord_2389000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389000).length < 2 ^ (prefixWord ++ tailWord_2389000).sum := by decide
  have hdescent : baseEnd_2389000 < baseStart_2389000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389024 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 2, 4]
def baseStart_2389024 : Nat := 118140960795 + 2389024 * 2 ^ 59
def prefixEnd_2389024 : Nat := 4983230072969 + 3 ^ 40 * 2389024 * 2
def baseEnd_2389024 : Nat := 408905869042322055437695

theorem tailTrace_2389024 : CollatzResearch.WordTrace tailWord_2389024 prefixEnd_2389024 408905869042322055437695 := by
  unfold tailWord_2389024
  simp only [CollatzResearch.WordTrace]
  refine ⟨43567431848490767830375063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58089909131321023773833417 43567431848490767830375063)
  ·
    refine ⟨65351147772736151745562595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43567431848490767830375063 65351147772736151745562595)
    ·
      refine ⟨98026721659104227618343893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65351147772736151745562595 98026721659104227618343893)
      ·
        refine ⟨2297501288885255334804935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 98026721659104227618343893 2297501288885255334804935)
        ·
          refine ⟨3446251933327883002207403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2297501288885255334804935 3446251933327883002207403)
          ·
            refine ⟨5169377899991824503311105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3446251933327883002207403 5169377899991824503311105)
            ·
              refine ⟨3877033424993868377483329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5169377899991824503311105 3877033424993868377483329)
              ·
                refine ⟨2907775068745401283112497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3877033424993868377483329 2907775068745401283112497)
                ·
                  refine ⟨2180831301559050962334373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2907775068745401283112497 2180831301559050962334373)
                  ·
                    refine ⟨408905869042322055437695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2180831301559050962334373 408905869042322055437695)
                    ·
                      rfl

theorem cell23_2389024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 2, 4].length) (baseStart_2389024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389024 prefixEnd_2389024 := by exact prefixLift 2389024
  have htrace : WordTrace (prefixWord ++ tailWord_2389024) baseStart_2389024 baseEnd_2389024 := by
    simpa [prefixWord, tailWord_2389024, baseEnd_2389024] using wordTrace_append hprefix tailTrace_2389024
  have hstable : (prefixWord ++ tailWord_2389024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389024).length < 2 ^ (prefixWord ++ tailWord_2389024).sum := by decide
  have hdescent : baseEnd_2389024 < baseStart_2389024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389040 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 5, 3, 2]
def baseStart_2389040 : Nat := 118140960795 + 2389040 * 2 ^ 59
def prefixEnd_2389040 : Nat := 4983230072969 + 3 ^ 40 * 2389040 * 2
def baseEnd_2389040 : Nat := 1226725822817438103713011

theorem tailTrace_2389040 : CollatzResearch.WordTrace tailWord_2389040 prefixEnd_2389040 1226725822817438103713011 := by
  unfold tailWord_2389040
  simp only [CollatzResearch.WordTrace]
  refine ⟨43567723632461785196666287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58090298176615713595555049 43567723632461785196666287)
  ·
    refine ⟨65351585448692677794999431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43567723632461785196666287 65351585448692677794999431)
    ·
      refine ⟨98027378173039016692499147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65351585448692677794999431 98027378173039016692499147)
      ·
        refine ⟨147041067259558525038748721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98027378173039016692499147 147041067259558525038748721)
        ·
          refine ⟨110280800444668893779061541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147041067259558525038748721 110280800444668893779061541)
          ·
            refine ⟨20677650083375417583574039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110280800444668893779061541 20677650083375417583574039)
            ·
              refine ⟨31016475125063126375361059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20677650083375417583574039 31016475125063126375361059)
              ·
                refine ⟨46524712687594689563041589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31016475125063126375361059 46524712687594689563041589)
                ·
                  refine ⟨4361691814462002146535149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46524712687594689563041589 4361691814462002146535149)
                  ·
                    refine ⟨1635634430423250804950681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4361691814462002146535149 1635634430423250804950681)
                    ·
                      refine ⟨1226725822817438103713011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635634430423250804950681 1226725822817438103713011)
                      ·
                        rfl

theorem cell23_2389040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 3, 2].length) (baseStart_2389040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389040 prefixEnd_2389040 := by exact prefixLift 2389040
  have htrace : WordTrace (prefixWord ++ tailWord_2389040) baseStart_2389040 baseEnd_2389040 := by
    simpa [prefixWord, tailWord_2389040, baseEnd_2389040] using wordTrace_append hprefix tailTrace_2389040
  have hstable : (prefixWord ++ tailWord_2389040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389040).length < 2 ^ (prefixWord ++ tailWord_2389040).sum := by decide
  have hdescent : baseEnd_2389040 < baseStart_2389040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389073 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_2389073 : Nat := 118140960795 + 2389073 * 2 ^ 59
def prefixEnd_2389073 : Nat := 4983230072969 + 3 ^ 40 * 2389073 * 2
def baseEnd_2389073 : Nat := 1226742767679036474600359

theorem tailTrace_2389073 : CollatzResearch.WordTrace tailWord_2389073 prefixEnd_2389073 1226742767679036474600359 := by
  unfold tailWord_2389073
  simp only [CollatzResearch.WordTrace]
  refine ⟨87136650873804017029283873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58091100582536011352855915 87136650873804017029283873)
  ·
    refine ⟨65352488155353012771962905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87136650873804017029283873 65352488155353012771962905)
    ·
      refine ⟨49014366116514759578972179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65352488155353012771962905 49014366116514759578972179)
      ·
        refine ⟨73521549174772139368458269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49014366116514759578972179 73521549174772139368458269)
        ·
          refine ⟨27570580940539552263171851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73521549174772139368458269 27570580940539552263171851)
          ·
            refine ⟨41355871410809328394757777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27570580940539552263171851 41355871410809328394757777)
            ·
              refine ⟨31016903558106996296068333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41355871410809328394757777 31016903558106996296068333)
              ·
                refine ⟨11631338834290123611025625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31016903558106996296068333 11631338834290123611025625)
                ·
                  refine ⟨8723504125717592708269219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11631338834290123611025625 8723504125717592708269219)
                  ·
                    refine ⟨13085256188576389062403829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8723504125717592708269219 13085256188576389062403829)
                    ·
                      refine ⟨1226742767679036474600359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13085256188576389062403829 1226742767679036474600359)
                      ·
                        rfl

theorem cell23_2389073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_2389073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389073 prefixEnd_2389073 := by exact prefixLift 2389073
  have htrace : WordTrace (prefixWord ++ tailWord_2389073) baseStart_2389073 baseEnd_2389073 := by
    simpa [prefixWord, tailWord_2389073, baseEnd_2389073] using wordTrace_append hprefix tailTrace_2389073
  have hstable : (prefixWord ++ tailWord_2389073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389073).length < 2 ^ (prefixWord ++ tailWord_2389073).sum := by decide
  have hdescent : baseEnd_2389073 < baseStart_2389073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389074 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_2389074 : Nat := 118140960795 + 2389074 * 2 ^ 59
def prefixEnd_2389074 : Nat := 4983230072969 + 3 ^ 40 * 2389074 * 2
def baseEnd_2389074 : Nat := 1226743281159690970687855

theorem tailTrace_2389074 : CollatzResearch.WordTrace tailWord_2389074 prefixEnd_2389074 1226743281159690970687855 := by
  unfold tailWord_2389074
  simp only [CollatzResearch.WordTrace]
  refine ⟨21784171836700098550017569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58091124897866929466713517 21784171836700098550017569)
  ·
    refine ⟨16338128877525073912513177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21784171836700098550017569 16338128877525073912513177)
    ·
      refine ⟨12253596658143805434384883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16338128877525073912513177 12253596658143805434384883)
      ·
        refine ⟨18380394987215708151577325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12253596658143805434384883 18380394987215708151577325)
        ·
          refine ⟨6892648120205890556841497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18380394987215708151577325 6892648120205890556841497)
          ·
            refine ⟨5169486090154417917631123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6892648120205890556841497 5169486090154417917631123)
            ·
              refine ⟨7754229135231626876446685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5169486090154417917631123 7754229135231626876446685)
              ·
                refine ⟨2907835925711860078667507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7754229135231626876446685 2907835925711860078667507)
                ·
                  refine ⟨4361753888567790118001261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907835925711860078667507 4361753888567790118001261)
                  ·
                    refine ⟨1635657708212921294250473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4361753888567790118001261 1635657708212921294250473)
                    ·
                      refine ⟨1226743281159690970687855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635657708212921294250473 1226743281159690970687855)
                      ·
                        rfl

theorem cell23_2389074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_2389074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389074 prefixEnd_2389074 := by exact prefixLift 2389074
  have htrace : WordTrace (prefixWord ++ tailWord_2389074) baseStart_2389074 baseEnd_2389074 := by
    simpa [prefixWord, tailWord_2389074, baseEnd_2389074] using wordTrace_append hprefix tailTrace_2389074
  have hstable : (prefixWord ++ tailWord_2389074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389074).length < 2 ^ (prefixWord ++ tailWord_2389074).sum := by decide
  have hdescent : baseEnd_2389074 < baseStart_2389074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389087 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 4, 2, 2]
def baseStart_2389087 : Nat := 118140960795 + 2389087 * 2 ^ 59
def prefixEnd_2389087 : Nat := 4983230072969 + 3 ^ 40 * 2389087 * 2
def baseEnd_2389087 : Nat := 1226749956408199419825295

theorem tailTrace_2389087 : CollatzResearch.WordTrace tailWord_2389087 prefixEnd_2389087 1226749956408199419825295 := by
  unfold tailWord_2389087
  simp only [CollatzResearch.WordTrace]
  refine ⟨87137161495753297420293515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58091440997168864946862343 87137161495753297420293515)
  ·
    refine ⟨130705742243629946130440273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87137161495753297420293515 130705742243629946130440273)
    ·
      refine ⟨98029306682722459597830205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130705742243629946130440273 98029306682722459597830205)
      ·
        refine ⟨36760990006020922349186327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98029306682722459597830205 36760990006020922349186327)
        ·
          refine ⟨55141485009031383523779491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36760990006020922349186327 55141485009031383523779491)
          ·
            refine ⟨82712227513547075285669237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55141485009031383523779491 82712227513547075285669237)
            ·
              refine ⟨7754271329395038308031491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82712227513547075285669237 7754271329395038308031491)
              ·
                refine ⟨11631406994092557462047237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7754271329395038308031491 11631406994092557462047237)
                ·
                  refine ⟨2180888811392354524133857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11631406994092557462047237 2180888811392354524133857)
                  ·
                    refine ⟨1635666608544265893100393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2180888811392354524133857 1635666608544265893100393)
                    ·
                      refine ⟨1226749956408199419825295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635666608544265893100393 1226749956408199419825295)
                      ·
                        rfl

theorem cell23_2389087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_2389087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389087 prefixEnd_2389087 := by exact prefixLift 2389087
  have htrace : WordTrace (prefixWord ++ tailWord_2389087) baseStart_2389087 baseEnd_2389087 := by
    simpa [prefixWord, tailWord_2389087, baseEnd_2389087] using wordTrace_append hprefix tailTrace_2389087
  have hstable : (prefixWord ++ tailWord_2389087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389087).length < 2 ^ (prefixWord ++ tailWord_2389087).sum := by decide
  have hdescent : baseEnd_2389087 < baseStart_2389087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389110 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_2389110 : Nat := 118140960795 + 2389110 * 2 ^ 59
def prefixEnd_2389110 : Nat := 4983230072969 + 3 ^ 40 * 2389110 * 2
def baseEnd_2389110 : Nat := 136306862940361425537521

theorem tailTrace_2389110 : CollatzResearch.WordTrace tailWord_2389110 prefixEnd_2389110 136306862940361425537521 := by
  unfold tailWord_2389110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5446125023416873271773799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58092000249779981565587189 5446125023416873271773799)
  ·
    refine ⟨8169187535125309907660699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5446125023416873271773799 8169187535125309907660699)
    ·
      refine ⟨12253781302687964861491049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8169187535125309907660699 12253781302687964861491049)
      ·
        refine ⟨9190335977015973646118287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12253781302687964861491049 9190335977015973646118287)
        ·
          refine ⟨13785503965523960469177431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9190335977015973646118287 13785503965523960469177431)
          ·
            refine ⟨20678255948285940703766147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13785503965523960469177431 20678255948285940703766147)
            ·
              refine ⟨31017383922428911055649221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20678255948285940703766147 31017383922428911055649221)
              ·
                refine ⟨5815759485455420822934229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31017383922428911055649221 5815759485455420822934229)
                ·
                  refine ⟨136306862940361425537521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5815759485455420822934229 136306862940361425537521)
                  ·
                    rfl

theorem cell23_2389110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_2389110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389110 prefixEnd_2389110 := by exact prefixLift 2389110
  have htrace : WordTrace (prefixWord ++ tailWord_2389110) baseStart_2389110 baseEnd_2389110 := by
    simpa [prefixWord, tailWord_2389110, baseEnd_2389110] using wordTrace_append hprefix tailTrace_2389110
  have hstable : (prefixWord ++ tailWord_2389110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389110).length < 2 ^ (prefixWord ++ tailWord_2389110).sum := by decide
  have hdescent : baseEnd_2389110 < baseStart_2389110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389123 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 1, 7]
def baseStart_2389123 : Nat := 118140960795 + 2389123 * 2 ^ 59
def prefixEnd_2389123 : Nat := 4983230072969 + 3 ^ 40 * 2389123 * 2
def baseEnd_2389123 : Nat := 408922813903920426325043

theorem tailTrace_2389123 : CollatzResearch.WordTrace tailWord_2389123 prefixEnd_2389123 408922813903920426325043 := by
  unfold tailWord_2389123
  simp only [CollatzResearch.WordTrace]
  refine ⟨87138474523622875568604023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58092316349081917045736015 87138474523622875568604023)
  ·
    refine ⟨130707711785434313352906035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87138474523622875568604023 130707711785434313352906035)
    ·
      refine ⟨196061567678151470029359053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130707711785434313352906035 196061567678151470029359053)
      ·
        refine ⟨73523087879306801261009645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196061567678151470029359053 73523087879306801261009645)
        ·
          refine ⟨27571157954740050472878617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73523087879306801261009645 27571157954740050472878617)
          ·
            refine ⟨20678368466055037854658963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27571157954740050472878617 20678368466055037854658963)
            ·
              refine ⟨31017552699082556781988445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20678368466055037854658963 31017552699082556781988445)
              ·
                refine ⟨11631582262155958793245667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31017552699082556781988445 11631582262155958793245667)
                ·
                  refine ⟨17447373393233938189868501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11631582262155958793245667 17447373393233938189868501)
                  ·
                    refine ⟨408922813903920426325043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17447373393233938189868501 408922813903920426325043)
                    ·
                      rfl

theorem cell23_2389123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 7].length) (baseStart_2389123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389123 prefixEnd_2389123 := by exact prefixLift 2389123
  have htrace : WordTrace (prefixWord ++ tailWord_2389123) baseStart_2389123 baseEnd_2389123 := by
    simpa [prefixWord, tailWord_2389123, baseEnd_2389123] using wordTrace_append hprefix tailTrace_2389123
  have hstable : (prefixWord ++ tailWord_2389123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389123).length < 2 ^ (prefixWord ++ tailWord_2389123).sum := by decide
  have hdescent : baseEnd_2389123 < baseStart_2389123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389144 : List Nat := [2, 1, 2, 4, 2, 2, 3, 2, 5]
def baseStart_2389144 : Nat := 118140960795 + 2389144 * 2 ^ 59
def prefixEnd_2389144 : Nat := 4983230072969 + 3 ^ 40 * 2389144 * 2
def baseEnd_2389144 : Nat := 136308802756167299645837

theorem tailTrace_2389144 : CollatzResearch.WordTrace tailWord_2389144 prefixEnd_2389144 136308802756167299645837 := by
  unfold tailWord_2389144
  simp only [CollatzResearch.WordTrace]
  refine ⟨43569620228273398077559243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58092826971031197436745657 43569620228273398077559243)
  ·
    refine ⟨65354430342410097116338865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43569620228273398077559243 65354430342410097116338865)
    ·
      refine ⟨49015822756807572837254149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65354430342410097116338865 49015822756807572837254149)
      ·
        refine ⟨9190466766901419906985153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49015822756807572837254149 9190466766901419906985153)
        ·
          refine ⟨6892850075176064930238865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9190466766901419906985153 6892850075176064930238865)
          ·
            refine ⟨5169637556382048697679149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6892850075176064930238865 5169637556382048697679149)
            ·
              refine ⟨1938614083643268261629681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5169637556382048697679149 1938614083643268261629681)
              ·
                refine ⟨1453960562732451196222261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1938614083643268261629681 1453960562732451196222261)
                ·
                  refine ⟨136308802756167299645837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1453960562732451196222261 136308802756167299645837)
                  ·
                    rfl

theorem cell23_2389144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 5].length) (baseStart_2389144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389144 prefixEnd_2389144 := by exact prefixLift 2389144
  have htrace : WordTrace (prefixWord ++ tailWord_2389144) baseStart_2389144 baseEnd_2389144 := by
    simpa [prefixWord, tailWord_2389144, baseEnd_2389144] using wordTrace_append hprefix tailTrace_2389144
  have hstable : (prefixWord ++ tailWord_2389144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389144).length < 2 ^ (prefixWord ++ tailWord_2389144).sum := by decide
  have hdescent : baseEnd_2389144 < baseStart_2389144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389177 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 4]
def baseStart_2389177 : Nat := 118140960795 + 2389177 * 2 ^ 59
def prefixEnd_2389177 : Nat := 4983230072969 + 3 ^ 40 * 2389177 * 2
def baseEnd_2389177 : Nat := 1226796169667104067699881

theorem tailTrace_2389177 : CollatzResearch.WordTrace tailWord_2389177 prefixEnd_2389177 1226796169667104067699881 := by
  unfold tailWord_2389177
  simp only [CollatzResearch.WordTrace]
  refine ⟨87140444065427242791069785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58093629376951495194046523 87140444065427242791069785)
  ·
    refine ⟨65355333049070432093302339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87140444065427242791069785 65355333049070432093302339)
    ·
      refine ⟨98032999573605648139953509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65355333049070432093302339 98032999573605648139953509)
      ·
        refine ⟨18381187420051059026241283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98032999573605648139953509 18381187420051059026241283)
        ·
          refine ⟨27571781130076588539361925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18381187420051059026241283 27571781130076588539361925)
          ·
            refine ⟨5169708961889360351130361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27571781130076588539361925 5169708961889360351130361)
            ·
              refine ⟨3877281721417020263347771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5169708961889360351130361 3877281721417020263347771)
              ·
                refine ⟨5815922582125530395021657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877281721417020263347771 5815922582125530395021657)
                ·
                  refine ⟨4361941936594147796266243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5815922582125530395021657 4361941936594147796266243)
                  ·
                    refine ⟨6542912904891221694399365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4361941936594147796266243 6542912904891221694399365)
                    ·
                      refine ⟨1226796169667104067699881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6542912904891221694399365 1226796169667104067699881)
                      ·
                        rfl

theorem cell23_2389177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_2389177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389177 prefixEnd_2389177 := by exact prefixLift 2389177
  have htrace : WordTrace (prefixWord ++ tailWord_2389177) baseStart_2389177 baseEnd_2389177 := by
    simpa [prefixWord, tailWord_2389177, baseEnd_2389177] using wordTrace_append hprefix tailTrace_2389177
  have hstable : (prefixWord ++ tailWord_2389177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389177).length < 2 ^ (prefixWord ++ tailWord_2389177).sum := by decide
  have hdescent : baseEnd_2389177 < baseStart_2389177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389183 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 10]
def baseStart_2389183 : Nat := 118140960795 + 2389183 * 2 ^ 59
def prefixEnd_2389183 : Nat := 4983230072969 + 3 ^ 40 * 2389183 * 2
def baseEnd_2389183 : Nat := 136311027839003449358317

theorem tailTrace_2389183 : CollatzResearch.WordTrace tailWord_2389183 prefixEnd_2389183 136311027839003449358317 := by
  unfold tailWord_2389183
  simp only [CollatzResearch.WordTrace]
  refine ⟨87140662903405505815788203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58093775268937003877192135 87140662903405505815788203)
  ·
    refine ⟨130710994355108258723682305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87140662903405505815788203 130710994355108258723682305)
    ·
      refine ⟨98033245766331194042761729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130710994355108258723682305 98033245766331194042761729)
      ·
        refine ⟨73524934324748395532071297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98033245766331194042761729 73524934324748395532071297)
        ·
          refine ⟨55143700743561296649053473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73524934324748395532071297 55143700743561296649053473)
          ·
            refine ⟨41357775557670972486790105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55143700743561296649053473 41357775557670972486790105)
            ·
              refine ⟨31018331668253229365092579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41357775557670972486790105 31018331668253229365092579)
              ·
                refine ⟨46527497502379844047638869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31018331668253229365092579 46527497502379844047638869)
                ·
                  refine ⟨136311027839003449358317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 46527497502379844047638869 136311027839003449358317)
                  ·
                    rfl

theorem cell23_2389183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 10].length) (baseStart_2389183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389183 prefixEnd_2389183 := by exact prefixLift 2389183
  have htrace : WordTrace (prefixWord ++ tailWord_2389183) baseStart_2389183 baseEnd_2389183 := by
    simpa [prefixWord, tailWord_2389183, baseEnd_2389183] using wordTrace_append hprefix tailTrace_2389183
  have hstable : (prefixWord ++ tailWord_2389183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389183).length < 2 ^ (prefixWord ++ tailWord_2389183).sum := by decide
  have hdescent : baseEnd_2389183 < baseStart_2389183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389203 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 8]
def baseStart_2389203 : Nat := 118140960795 + 2389203 * 2 ^ 59
def prefixEnd_2389203 : Nat := 4983230072969 + 3 ^ 40 * 2389203 * 2
def baseEnd_2389203 : Nat := 1226809520164120965974761

theorem tailTrace_2389203 : CollatzResearch.WordTrace tailWord_2389203 prefixEnd_2389203 1226809520164120965974761 := by
  unfold tailWord_2389203
  simp only [CollatzResearch.WordTrace]
  refine ⟨87141392363333049231516263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58094261575555366154344175 87141392363333049231516263)
  ·
    refine ⟨130712088544999573847274395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87141392363333049231516263 130712088544999573847274395)
    ·
      refine ⟨196068132817499360770911593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130712088544999573847274395 196068132817499360770911593)
      ·
        refine ⟨147051099613124520578183695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196068132817499360770911593 147051099613124520578183695)
        ·
          refine ⟨220576649419686780867275543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147051099613124520578183695 220576649419686780867275543)
          ·
            refine ⟨330864974129530171300913315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220576649419686780867275543 330864974129530171300913315)
            ·
              refine ⟨496297461194295256951369973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330864974129530171300913315 496297461194295256951369973)
              ·
                refine ⟨46527886986965180339190935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 496297461194295256951369973 46527886986965180339190935)
                ·
                  refine ⟨69791830480447770508786403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46527886986965180339190935 69791830480447770508786403)
                  ·
                    refine ⟨104687745720671655763179605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69791830480447770508786403 104687745720671655763179605)
                    ·
                      refine ⟨1226809520164120965974761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 104687745720671655763179605 1226809520164120965974761)
                      ·
                        rfl

theorem cell23_2389203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_2389203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389203 prefixEnd_2389203 := by exact prefixLift 2389203
  have htrace : WordTrace (prefixWord ++ tailWord_2389203) baseStart_2389203 baseEnd_2389203 := by
    simpa [prefixWord, tailWord_2389203, baseEnd_2389203] using wordTrace_append hprefix tailTrace_2389203
  have hstable : (prefixWord ++ tailWord_2389203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389203).length < 2 ^ (prefixWord ++ tailWord_2389203).sum := by decide
  have hdescent : baseEnd_2389203 < baseStart_2389203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389210 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3]
def baseStart_2389210 : Nat := 118140960795 + 2389210 * 2 ^ 59
def prefixEnd_2389210 : Nat := 4983230072969 + 3 ^ 40 * 2389210 * 2
def baseEnd_2389210 : Nat := 1226813114528702438587229

theorem tailTrace_2389210 : CollatzResearch.WordTrace tailWord_2389210 prefixEnd_2389210 1226813114528702438587229 := by
  unfold tailWord_2389210
  simp only [CollatzResearch.WordTrace]
  refine ⟨21785411918576922356755271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58094431782871792951347389 21785411918576922356755271)
  ·
    refine ⟨32678117877865383535132907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21785411918576922356755271 32678117877865383535132907)
    ·
      refine ⟨49017176816798075302699361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32678117877865383535132907 49017176816798075302699361)
      ·
        refine ⟨36762882612598556477024521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49017176816798075302699361 36762882612598556477024521)
        ·
          refine ⟨27572161959448917357768391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36762882612598556477024521 27572161959448917357768391)
          ·
            refine ⟨41358242939173376036652587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27572161959448917357768391 41358242939173376036652587)
            ·
              refine ⟨62037364408760064054978881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41358242939173376036652587 62037364408760064054978881)
              ·
                refine ⟨46528023306570048041234161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62037364408760064054978881 46528023306570048041234161)
                ·
                  refine ⟨34896017479927536030925621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46528023306570048041234161 34896017479927536030925621)
                  ·
                    refine ⟨3271501638743206502899277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34896017479927536030925621 3271501638743206502899277)
                    ·
                      refine ⟨1226813114528702438587229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3271501638743206502899277 1226813114528702438587229)
                      ·
                        rfl

theorem cell23_2389210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_2389210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389210 prefixEnd_2389210 := by exact prefixLift 2389210
  have htrace : WordTrace (prefixWord ++ tailWord_2389210) baseStart_2389210 baseEnd_2389210 := by
    simpa [prefixWord, tailWord_2389210, baseEnd_2389210] using wordTrace_append hprefix tailTrace_2389210
  have hstable : (prefixWord ++ tailWord_2389210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389210).length < 2 ^ (prefixWord ++ tailWord_2389210).sum := by decide
  have hdescent : baseEnd_2389210 < baseStart_2389210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389227 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 5, 1, 3]
def baseStart_2389227 : Nat := 118140960795 + 2389227 * 2 ^ 59
def prefixEnd_2389227 : Nat := 4983230072969 + 3 ^ 40 * 2389227 * 2
def baseEnd_2389227 : Nat := 1226821843699828872074651

theorem tailTrace_2389227 : CollatzResearch.WordTrace tailWord_2389227 prefixEnd_2389227 1226821843699828872074651 := by
  unfold tailWord_2389227
  simp only [CollatzResearch.WordTrace]
  refine ⟨87142267715246101330389935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58094845143497400886926623 87142267715246101330389935)
  ·
    refine ⟨130713401572869151995584903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87142267715246101330389935 130713401572869151995584903)
    ·
      refine ⟨196070102359303727993377355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130713401572869151995584903 196070102359303727993377355)
      ·
        refine ⟨294105153538955591990066033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196070102359303727993377355 294105153538955591990066033)
        ·
          refine ⟨220578865154216693992549525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294105153538955591990066033 220578865154216693992549525)
          ·
            refine ⟨10339634304103907530900759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 220578865154216693992549525 10339634304103907530900759)
            ·
              refine ⟨15509451456155861296351139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10339634304103907530900759 15509451456155861296351139)
              ·
                refine ⟨23264177184233791944526709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15509451456155861296351139 23264177184233791944526709)
                ·
                  refine ⟨2181016611021917994799379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23264177184233791944526709 2181016611021917994799379)
                  ·
                    refine ⟨3271524916532876992199069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2181016611021917994799379 3271524916532876992199069)
                    ·
                      refine ⟨1226821843699828872074651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3271524916532876992199069 1226821843699828872074651)
                      ·
                        rfl

theorem cell23_2389227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 1, 3].length) (baseStart_2389227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389227 prefixEnd_2389227 := by exact prefixLift 2389227
  have htrace : WordTrace (prefixWord ++ tailWord_2389227) baseStart_2389227 baseEnd_2389227 := by
    simpa [prefixWord, tailWord_2389227, baseEnd_2389227] using wordTrace_append hprefix tailTrace_2389227
  have hstable : (prefixWord ++ tailWord_2389227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389227).length < 2 ^ (prefixWord ++ tailWord_2389227).sum := by decide
  have hdescent : baseEnd_2389227 < baseStart_2389227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389231 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 2, 2, 3]
def baseStart_2389231 : Nat := 118140960795 + 2389231 * 2 ^ 59
def prefixEnd_2389231 : Nat := 4983230072969 + 3 ^ 40 * 2389231 * 2
def baseEnd_2389231 : Nat := 1226823897622446856424633

theorem tailTrace_2389231 : CollatzResearch.WordTrace tailWord_2389231 prefixEnd_2389231 1226823897622446856424633 := by
  unfold tailWord_2389231
  simp only [CollatzResearch.WordTrace]
  refine ⟨87142413607231610013535547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58094942404821073342357031 87142413607231610013535547)
  ·
    refine ⟨130713620410847415020303321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87142413607231610013535547 130713620410847415020303321)
    ·
      refine ⟨98035215308135561265227491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130713620410847415020303321 98035215308135561265227491)
      ·
        refine ⟨147052822962203341897841237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98035215308135561265227491 147052822962203341897841237)
        ·
          refine ⟨1723275269088320412865327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 147052822962203341897841237 1723275269088320412865327)
          ·
            refine ⟨2584912903632480619297991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723275269088320412865327 2584912903632480619297991)
            ·
              refine ⟨3877369355448720928946987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2584912903632480619297991 3877369355448720928946987)
              ·
                refine ⟨5816054033173081393420481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877369355448720928946987 5816054033173081393420481)
                ·
                  refine ⟨4362040524879811045065361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5816054033173081393420481 4362040524879811045065361)
                  ·
                    refine ⟨3271530393659858283799021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4362040524879811045065361 3271530393659858283799021)
                    ·
                      refine ⟨1226823897622446856424633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3271530393659858283799021 1226823897622446856424633)
                      ·
                        rfl

theorem cell23_2389231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 2, 3].length) (baseStart_2389231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389231 prefixEnd_2389231 := by exact prefixLift 2389231
  have htrace : WordTrace (prefixWord ++ tailWord_2389231) baseStart_2389231 baseEnd_2389231 := by
    simpa [prefixWord, tailWord_2389231, baseEnd_2389231] using wordTrace_append hprefix tailTrace_2389231
  have hstable : (prefixWord ++ tailWord_2389231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389231).length < 2 ^ (prefixWord ++ tailWord_2389231).sum := by decide
  have hdescent : baseEnd_2389231 < baseStart_2389231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389247 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 1, 5]
def baseStart_2389247 : Nat := 118140960795 + 2389247 * 2 ^ 59
def prefixEnd_2389247 : Nat := 4983230072969 + 3 ^ 40 * 2389247 * 2
def baseEnd_2389247 : Nat := 408944037770972931274853

theorem tailTrace_2389247 : CollatzResearch.WordTrace tailWord_2389247 prefixEnd_2389247 408944037770972931274853 := by
  unfold tailWord_2389247
  simp only [CollatzResearch.WordTrace]
  refine ⟨87142997175173644746117995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58095331450115763164078663 87142997175173644746117995)
  ·
    refine ⟨130714495762760467119176993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87142997175173644746117995 130714495762760467119176993)
    ·
      refine ⟨98035871822070350339382745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130714495762760467119176993 98035871822070350339382745)
      ·
        refine ⟨73526903866552762754537059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98035871822070350339382745 73526903866552762754537059)
        ·
          refine ⟨110290355799829144131805589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73526903866552762754537059 110290355799829144131805589)
          ·
            refine ⟨5169860428116991131178387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110290355799829144131805589 5169860428116991131178387)
            ·
              refine ⟨7754790642175486696767581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5169860428116991131178387 7754790642175486696767581)
              ·
                refine ⟨2908046490815807511287843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7754790642175486696767581 2908046490815807511287843)
                ·
                  refine ⟨4362069736223711266931765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908046490815807511287843 4362069736223711266931765)
                  ·
                    refine ⟨408944037770972931274853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4362069736223711266931765 408944037770972931274853)
                    ·
                      rfl

theorem cell23_2389247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 5].length) (baseStart_2389247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389247 prefixEnd_2389247 := by exact prefixLift 2389247
  have htrace : WordTrace (prefixWord ++ tailWord_2389247) baseStart_2389247 baseEnd_2389247 := by
    simpa [prefixWord, tailWord_2389247, baseEnd_2389247] using wordTrace_append hprefix tailTrace_2389247
  have hstable : (prefixWord ++ tailWord_2389247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389247).length < 2 ^ (prefixWord ++ tailWord_2389247).sum := by decide
  have hdescent : baseEnd_2389247 < baseStart_2389247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389284 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_2389284 : Nat := 118140960795 + 2389284 * 2 ^ 59
def prefixEnd_2389284 : Nat := 4983230072969 + 3 ^ 40 * 2389284 * 2
def baseEnd_2389284 : Nat := 1226851112097135149061889

theorem tailTrace_2389284 : CollatzResearch.WordTrace tailWord_2389284 prefixEnd_2389284 1226851112097135149061889 := by
  unfold tailWord_2389284
  simp only [CollatzResearch.WordTrace]
  refine ⟨43572173338019800032607453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58096231117359733376809937 43572173338019800032607453)
  ·
    refine ⟨16339565001757425012227795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43572173338019800032607453 16339565001757425012227795)
    ·
      refine ⟨24509347502636137518341693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16339565001757425012227795 24509347502636137518341693)
      ·
        refine ⟨9191005313488551569378135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24509347502636137518341693 9191005313488551569378135)
        ·
          refine ⟨13786507970232827354067203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9191005313488551569378135 13786507970232827354067203)
          ·
            refine ⟨20679761955349241031100805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13786507970232827354067203 20679761955349241031100805)
            ·
              refine ⟨3877455366627982693331401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20679761955349241031100805 3877455366627982693331401)
              ·
                refine ⟨2908091524970987019998551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3877455366627982693331401 2908091524970987019998551)
                ·
                  refine ⟨4362137287456480529997827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908091524970987019998551 4362137287456480529997827)
                  ·
                    refine ⟨6543205931184720794996741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4362137287456480529997827 6543205931184720794996741)
                    ·
                      refine ⟨1226851112097135149061889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6543205931184720794996741 1226851112097135149061889)
                      ·
                        rfl

theorem cell23_2389284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_2389284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389284 prefixEnd_2389284 := by exact prefixLift 2389284
  have htrace : WordTrace (prefixWord ++ tailWord_2389284) baseStart_2389284 baseEnd_2389284 := by
    simpa [prefixWord, tailWord_2389284, baseEnd_2389284] using wordTrace_append hprefix tailTrace_2389284
  have hstable : (prefixWord ++ tailWord_2389284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389284).length < 2 ^ (prefixWord ++ tailWord_2389284).sum := by decide
  have hdescent : baseEnd_2389284 < baseStart_2389284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389320 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 2, 7]
def baseStart_2389320 : Nat := 118140960795 + 2389320 * 2 ^ 59
def prefixEnd_2389320 : Nat := 4983230072969 + 3 ^ 40 * 2389320 * 2
def baseEnd_2389320 : Nat := 408956532466899002737241

theorem tailTrace_2389320 : CollatzResearch.WordTrace tailWord_2389320 prefixEnd_2389320 408956532466899002737241 := by
  unfold tailWord_2389320
  simp only [CollatzResearch.WordTrace]
  refine ⟨43572829851954589106762707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58097106469272785475683609 43572829851954589106762707)
  ·
    refine ⟨65359244777931883660144061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43572829851954589106762707 65359244777931883660144061)
    ·
      refine ⟨24509716791724456372554023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65359244777931883660144061 24509716791724456372554023)
      ·
        refine ⟨36764575187586684558831035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24509716791724456372554023 36764575187586684558831035)
        ·
          refine ⟨55146862781380026838246553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36764575187586684558831035 55146862781380026838246553)
          ·
            refine ⟨41360147086035020128684915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55146862781380026838246553 41360147086035020128684915)
            ·
              refine ⟨62040220629052530193027373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41360147086035020128684915 62040220629052530193027373)
              ·
                refine ⟨23265082735894698822385265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62040220629052530193027373 23265082735894698822385265)
                ·
                  refine ⟨17448812051921024116788949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23265082735894698822385265 17448812051921024116788949)
                  ·
                    refine ⟨408956532466899002737241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17448812051921024116788949 408956532466899002737241)
                    ·
                      rfl

theorem cell23_2389320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_2389320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389320 prefixEnd_2389320 := by exact prefixLift 2389320
  have htrace : WordTrace (prefixWord ++ tailWord_2389320) baseStart_2389320 baseEnd_2389320 := by
    simpa [prefixWord, tailWord_2389320, baseEnd_2389320] using wordTrace_append hprefix tailTrace_2389320
  have hstable : (prefixWord ++ tailWord_2389320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389320).length < 2 ^ (prefixWord ++ tailWord_2389320).sum := by decide
  have hdescent : baseEnd_2389320 < baseStart_2389320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389378 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_2389378 : Nat := 118140960795 + 2389378 * 2 ^ 59
def prefixEnd_2389378 : Nat := 4983230072969 + 3 ^ 40 * 2389378 * 2
def baseEnd_2389378 : Nat := 1226899379278657781286457

theorem tailTrace_2389378 : CollatzResearch.WordTrace tailWord_2389378 prefixEnd_2389378 1226899379278657781286457 := by
  unfold tailWord_2389378
  simp only [CollatzResearch.WordTrace]
  refine ⟨21786943784424763529784197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58098516758466036079424525 21786943784424763529784197)
  ·
    refine ⟨4085051959579643161834537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21786943784424763529784197 4085051959579643161834537)
    ·
      refine ⟨3063788969684732371375903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4085051959579643161834537 3063788969684732371375903)
      ·
        refine ⟨4595683454527098557063855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063788969684732371375903 4595683454527098557063855)
        ·
          refine ⟨6893525181790647835595783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595683454527098557063855 6893525181790647835595783)
          ·
            refine ⟨10340287772685971753393675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6893525181790647835595783 10340287772685971753393675)
            ·
              refine ⟨15510431659028957630090513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10340287772685971753393675 15510431659028957630090513)
              ·
                refine ⟨11632823744271718222567885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15510431659028957630090513 11632823744271718222567885)
                ·
                  refine ⟨4362308904101894333462957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11632823744271718222567885 4362308904101894333462957)
                  ·
                    refine ⟨1635865839038210375048609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4362308904101894333462957 1635865839038210375048609)
                    ·
                      refine ⟨1226899379278657781286457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635865839038210375048609 1226899379278657781286457)
                      ·
                        rfl

theorem cell23_2389378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_2389378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389378 prefixEnd_2389378 := by exact prefixLift 2389378
  have htrace : WordTrace (prefixWord ++ tailWord_2389378) baseStart_2389378 baseEnd_2389378 := by
    simpa [prefixWord, tailWord_2389378, baseEnd_2389378] using wordTrace_append hprefix tailTrace_2389378
  have hstable : (prefixWord ++ tailWord_2389378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389378).length < 2 ^ (prefixWord ++ tailWord_2389378).sum := by decide
  have hdescent : baseEnd_2389378 < baseStart_2389378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389387 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 4]
def baseStart_2389387 : Nat := 118140960795 + 2389387 * 2 ^ 59
def prefixEnd_2389387 : Nat := 4983230072969 + 3 ^ 40 * 2389387 * 2
def baseEnd_2389387 : Nat := 1226904000604548246073915

theorem tailTrace_2389387 : CollatzResearch.WordTrace tailWord_2389387 prefixEnd_2389387 1226904000604548246073915 := by
  unfold tailWord_2389387
  simp only [CollatzResearch.WordTrace]
  refine ⟨87148103394666448656214415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58098735596444299104142943 87148103394666448656214415)
  ·
    refine ⟨130722155091999672984321623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87148103394666448656214415 130722155091999672984321623)
    ·
      refine ⟨196083232637999509476482435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130722155091999672984321623 196083232637999509476482435)
      ·
        refine ⟨294124848956999264214723653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196083232637999509476482435 294124848956999264214723653)
        ·
          refine ⟨55148409179437362040260685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 294124848956999264214723653 55148409179437362040260685)
          ·
            refine ⟨20680653442289010765097757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55148409179437362040260685 20680653442289010765097757)
            ·
              refine ⟨7755245040858379036911659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20680653442289010765097757 7755245040858379036911659)
              ·
                refine ⟨11632867561287568555367489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7755245040858379036911659 11632867561287568555367489)
                ·
                  refine ⟨8724650670965676416525617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11632867561287568555367489 8724650670965676416525617)
                  ·
                    refine ⟨6543488003224257312394213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8724650670965676416525617 6543488003224257312394213)
                    ·
                      refine ⟨1226904000604548246073915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6543488003224257312394213 1226904000604548246073915)
                      ·
                        rfl

theorem cell23_2389387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 4].length) (baseStart_2389387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389387 prefixEnd_2389387 := by exact prefixLift 2389387
  have htrace : WordTrace (prefixWord ++ tailWord_2389387) baseStart_2389387 baseEnd_2389387 := by
    simpa [prefixWord, tailWord_2389387, baseEnd_2389387] using wordTrace_append hprefix tailTrace_2389387
  have hstable : (prefixWord ++ tailWord_2389387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389387).length < 2 ^ (prefixWord ++ tailWord_2389387).sum := by decide
  have hdescent : baseEnd_2389387 < baseStart_2389387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389427 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 2, 5]
def baseStart_2389427 : Nat := 118140960795 + 2389427 * 2 ^ 59
def prefixEnd_2389427 : Nat := 4983230072969 + 3 ^ 40 * 2389427 * 2
def baseEnd_2389427 : Nat := 408974846610242696524577

theorem tailTrace_2389427 : CollatzResearch.WordTrace tailWord_2389427 prefixEnd_2389427 408974846610242696524577 := by
  unfold tailWord_2389427
  simp only [CollatzResearch.WordTrace]
  refine ⟨87149562314521535487670535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58099708209681023658447023 87149562314521535487670535)
  ·
    refine ⟨130724343471782303231505803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87149562314521535487670535 130724343471782303231505803)
    ·
      refine ⟨196086515207673454847258705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130724343471782303231505803 196086515207673454847258705)
      ·
        refine ⟨147064886405755091135444029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196086515207673454847258705 147064886405755091135444029)
        ·
          refine ⟨55149332402158159175791511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147064886405755091135444029 55149332402158159175791511)
          ·
            refine ⟨82723998603237238763687267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55149332402158159175791511 82723998603237238763687267)
            ·
              refine ⟨124085997904855858145530901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82723998603237238763687267 124085997904855858145530901)
              ·
                refine ⟨5816531151790118350571761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124085997904855858145530901 5816531151790118350571761)
                ·
                  refine ⟨4362398363842588762928821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5816531151790118350571761 4362398363842588762928821)
                  ·
                    refine ⟨408974846610242696524577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4362398363842588762928821 408974846610242696524577)
                    ·
                      rfl

theorem cell23_2389427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 5].length) (baseStart_2389427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389427 prefixEnd_2389427 := by exact prefixLift 2389427
  have htrace : WordTrace (prefixWord ++ tailWord_2389427) baseStart_2389427 baseEnd_2389427 := by
    simpa [prefixWord, tailWord_2389427, baseEnd_2389427] using wordTrace_append hprefix tailTrace_2389427
  have hstable : (prefixWord ++ tailWord_2389427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389427).length < 2 ^ (prefixWord ++ tailWord_2389427).sum := by decide
  have hdescent : baseEnd_2389427 < baseStart_2389427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389437 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_2389437 : Nat := 118140960795 + 2389437 * 2 ^ 59
def prefixEnd_2389437 : Nat := 4983230072969 + 3 ^ 40 * 2389437 * 2
def baseEnd_2389437 : Nat := 1226929674637273050448685

theorem tailTrace_2389437 : CollatzResearch.WordTrace tailWord_2389437 prefixEnd_2389437 1226929674637273050448685 := by
  unfold tailWord_2389437
  simp only [CollatzResearch.WordTrace]
  refine ⟨87149927044485307195534565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58099951362990204797023043 87149927044485307195534565)
  ·
    refine ⟨16340611320840995099162731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87149927044485307195534565 16340611320840995099162731)
    ·
      refine ⟨24510916981261492648744097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16340611320840995099162731 24510916981261492648744097)
      ·
        refine ⟨18383187735946119486558073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24510916981261492648744097 18383187735946119486558073)
        ·
          refine ⟨13787390801959589614918555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18383187735946119486558073 13787390801959589614918555)
          ·
            refine ⟨20681086202939384422377833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13787390801959589614918555 20681086202939384422377833)
            ·
              refine ⟨15510814652204538316783375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20681086202939384422377833 15510814652204538316783375)
              ·
                refine ⟨23266221978306807475175063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15510814652204538316783375 23266221978306807475175063)
                ·
                  refine ⟨34899332967460211212762595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23266221978306807475175063 34899332967460211212762595)
                  ·
                    refine ⟨52348999451190316819143893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34899332967460211212762595 52348999451190316819143893)
                    ·
                      refine ⟨1226929674637273050448685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52348999451190316819143893 1226929674637273050448685)
                      ·
                        rfl

theorem cell23_2389437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_2389437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389437 prefixEnd_2389437 := by exact prefixLift 2389437
  have htrace : WordTrace (prefixWord ++ tailWord_2389437) baseStart_2389437 baseEnd_2389437 := by
    simpa [prefixWord, tailWord_2389437, baseEnd_2389437] using wordTrace_append hprefix tailTrace_2389437
  have hstable : (prefixWord ++ tailWord_2389437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389437).length < 2 ^ (prefixWord ++ tailWord_2389437).sum := by decide
  have hdescent : baseEnd_2389437 < baseStart_2389437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389444 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_2389444 : Nat := 118140960795 + 2389444 * 2 ^ 59
def prefixEnd_2389444 : Nat := 4983230072969 + 3 ^ 40 * 2389444 * 2
def baseEnd_2389444 : Nat := 408977756333951507687051

theorem tailTrace_2389444 : CollatzResearch.WordTrace tailWord_2389444 prefixEnd_2389444 408977756333951507687051 := by
  unfold tailWord_2389444
  simp only [CollatzResearch.WordTrace]
  refine ⟨43575091177729973695519693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58100121570306631594026257 43575091177729973695519693)
  ·
    refine ⟨16340659191648740135819885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43575091177729973695519693 16340659191648740135819885)
    ·
      refine ⟨6127747196868277550932457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16340659191648740135819885 6127747196868277550932457)
      ·
        refine ⟨4595810397651208163199343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6127747196868277550932457 4595810397651208163199343)
        ·
          refine ⟨6893715596476812244799015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595810397651208163199343 6893715596476812244799015)
          ·
            refine ⟨10340573394715218367198523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6893715596476812244799015 10340573394715218367198523)
            ·
              refine ⟨15510860092072827550797785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10340573394715218367198523 15510860092072827550797785)
              ·
                refine ⟨11633145069054620663098339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15510860092072827550797785 11633145069054620663098339)
                ·
                  refine ⟨17449717603581930994647509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11633145069054620663098339 17449717603581930994647509)
                  ·
                    refine ⟨408977756333951507687051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17449717603581930994647509 408977756333951507687051)
                    ·
                      rfl

theorem cell23_2389444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_2389444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389444 prefixEnd_2389444 := by exact prefixLift 2389444
  have htrace : WordTrace (prefixWord ++ tailWord_2389444) baseStart_2389444 baseEnd_2389444 := by
    simpa [prefixWord, tailWord_2389444, baseEnd_2389444] using wordTrace_append hprefix tailTrace_2389444
  have hstable : (prefixWord ++ tailWord_2389444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389444).length < 2 ^ (prefixWord ++ tailWord_2389444).sum := by decide
  have hdescent : baseEnd_2389444 < baseStart_2389444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389447 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_2389447 : Nat := 118140960795 + 2389447 * 2 ^ 59
def prefixEnd_2389447 : Nat := 4983230072969 + 3 ^ 40 * 2389447 * 2
def baseEnd_2389447 : Nat := 1226934809443818011323639

theorem tailTrace_2389447 : CollatzResearch.WordTrace tailWord_2389447 prefixEnd_2389447 1226934809443818011323639 := by
  unfold tailWord_2389447
  simp only [CollatzResearch.WordTrace]
  refine ⟨87150291774449078903398595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58100194516299385935599063 87150291774449078903398595)
  ·
    refine ⟨130725437661673618355097893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87150291774449078903398595 130725437661673618355097893)
    ·
      refine ⟨24511019561563803441580855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130725437661673618355097893 24511019561563803441580855)
      ·
        refine ⟨36766529342345705162371283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24511019561563803441580855 36766529342345705162371283)
        ·
          refine ⟨55149794013518557743556925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36766529342345705162371283 55149794013518557743556925)
          ·
            refine ⟨20681172755069459153833847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55149794013518557743556925 20681172755069459153833847)
            ·
              refine ⟨31021759132604188730750771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20681172755069459153833847 31021759132604188730750771)
              ·
                refine ⟨46532638698906283096126157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31021759132604188730750771 46532638698906283096126157)
                ·
                  refine ⟨17449739512089856161047309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46532638698906283096126157 17449739512089856161047309)
                  ·
                    refine ⟨6543652317033696060392741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17449739512089856161047309 6543652317033696060392741)
                    ·
                      refine ⟨1226934809443818011323639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6543652317033696060392741 1226934809443818011323639)
                      ·
                        rfl

theorem cell23_2389447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_2389447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389447 prefixEnd_2389447 := by exact prefixLift 2389447
  have htrace : WordTrace (prefixWord ++ tailWord_2389447) baseStart_2389447 baseEnd_2389447 := by
    simpa [prefixWord, tailWord_2389447, baseEnd_2389447] using wordTrace_append hprefix tailTrace_2389447
  have hstable : (prefixWord ++ tailWord_2389447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389447).length < 2 ^ (prefixWord ++ tailWord_2389447).sum := by decide
  have hdescent : baseEnd_2389447 < baseStart_2389447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389464 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 1, 6, 2]
def baseStart_2389464 : Nat := 118140960795 + 2389464 * 2 ^ 59
def prefixEnd_2389464 : Nat := 4983230072969 + 3 ^ 40 * 2389464 * 2
def baseEnd_2389464 : Nat := 1226943538614944444811061

theorem tailTrace_2389464 : CollatzResearch.WordTrace tailWord_2389464 prefixEnd_2389464 1226943538614944444811061 := by
  unfold tailWord_2389464
  simp only [CollatzResearch.WordTrace]
  refine ⟨43575455907693745403383723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58100607876924993871178297 43575455907693745403383723)
  ·
    refine ⟨65363183861540618105075585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43575455907693745403383723 65363183861540618105075585)
    ·
      refine ⟨49022387896155463578806689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65363183861540618105075585 49022387896155463578806689)
      ·
        refine ⟨36766790922116597684105017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49022387896155463578806689 36766790922116597684105017)
        ·
          refine ⟨27575093191587448263078763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36766790922116597684105017 27575093191587448263078763)
          ·
            refine ⟨41362639787381172394618145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27575093191587448263078763 41362639787381172394618145)
            ·
              refine ⟨31021979840535879295963609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41362639787381172394618145 31021979840535879295963609)
              ·
                refine ⟨23266484880401909471972707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31021979840535879295963609 23266484880401909471972707)
                ·
                  refine ⟨34899727320602864207959061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23266484880401909471972707 34899727320602864207959061)
                  ·
                    refine ⟨1635924718153259259748081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34899727320602864207959061 1635924718153259259748081)
                    ·
                      refine ⟨1226943538614944444811061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635924718153259259748081 1226943538614944444811061)
                      ·
                        rfl

theorem cell23_2389464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_2389464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389464 prefixEnd_2389464 := by exact prefixLift 2389464
  have htrace : WordTrace (prefixWord ++ tailWord_2389464) baseStart_2389464 baseEnd_2389464 := by
    simpa [prefixWord, tailWord_2389464, baseEnd_2389464] using wordTrace_append hprefix tailTrace_2389464
  have hstable : (prefixWord ++ tailWord_2389464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389464).length < 2 ^ (prefixWord ++ tailWord_2389464).sum := by decide
  have hdescent : baseEnd_2389464 < baseStart_2389464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389487 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 8]
def baseStart_2389487 : Nat := 118140960795 + 2389487 * 2 ^ 59
def prefixEnd_2389487 : Nat := 4983230072969 + 3 ^ 40 * 2389487 * 2
def baseEnd_2389487 : Nat := 136328372074444206091495

theorem tailTrace_2389487 : CollatzResearch.WordTrace tailWord_2389487 prefixEnd_2389487 136328372074444206091495 := by
  unfold tailWord_2389487
  simp only [CollatzResearch.WordTrace]
  refine ⟨87151750694304165734854715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58101167129536110489903143 87151750694304165734854715)
  ·
    refine ⟨130727626041456248602282073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87151750694304165734854715 130727626041456248602282073)
    ·
      refine ⟨98045719531092186451711555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130727626041456248602282073 98045719531092186451711555)
      ·
        refine ⟨147068579296638279677567333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98045719531092186451711555 147068579296638279677567333)
        ·
          refine ⟨27575358618119677439543875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147068579296638279677567333 27575358618119677439543875)
          ·
            refine ⟨41363037927179516159315813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27575358618119677439543875 41363037927179516159315813)
            ·
              refine ⟨7755569611346159279871715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41363037927179516159315813 7755569611346159279871715)
              ·
                refine ⟨11633354417019238919807573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7755569611346159279871715 11633354417019238919807573)
                ·
                  refine ⟨136328372074444206091495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11633354417019238919807573 136328372074444206091495)
                  ·
                    rfl

theorem cell23_2389487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 8].length) (baseStart_2389487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389487 prefixEnd_2389487 := by exact prefixLift 2389487
  have htrace : WordTrace (prefixWord ++ tailWord_2389487) baseStart_2389487 baseEnd_2389487 := by
    simpa [prefixWord, tailWord_2389487, baseEnd_2389487] using wordTrace_append hprefix tailTrace_2389487
  have hstable : (prefixWord ++ tailWord_2389487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389487).length < 2 ^ (prefixWord ++ tailWord_2389487).sum := by decide
  have hdescent : baseEnd_2389487 < baseStart_2389487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389518 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_2389518 : Nat := 118140960795 + 2389518 * 2 ^ 59
def prefixEnd_2389518 : Nat := 4983230072969 + 3 ^ 40 * 2389518 * 2
def baseEnd_2389518 : Nat := 1226971266570287233535813

theorem tailTrace_2389518 : CollatzResearch.WordTrace tailWord_2389518 prefixEnd_2389518 1226971266570287233535813 := by
  unfold tailWord_2389518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10894110169648982253654151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58101920904794572019488805 10894110169648982253654151)
  ·
    refine ⟨16341165254473473380481227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10894110169648982253654151 16341165254473473380481227)
    ·
      refine ⟨24511747881710210070721841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16341165254473473380481227 24511747881710210070721841)
      ·
        refine ⟨18383810911282657553041381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24511747881710210070721841 18383810911282657553041381)
        ·
          refine ⟨3446964545865498291195259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18383810911282657553041381 3446964545865498291195259)
          ·
            refine ⟨5170446818798247436792889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3446964545865498291195259 5170446818798247436792889)
            ·
              refine ⟨3877835114098685577594667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5170446818798247436792889 3877835114098685577594667)
              ·
                refine ⟨5816752671148028366392001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877835114098685577594667 5816752671148028366392001)
                ·
                  refine ⟨4362564503361021274794001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5816752671148028366392001 4362564503361021274794001)
                  ·
                    refine ⟨3271923377520765956095501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4362564503361021274794001 3271923377520765956095501)
                    ·
                      refine ⟨1226971266570287233535813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3271923377520765956095501 1226971266570287233535813)
                      ·
                        rfl

theorem cell23_2389518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_2389518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389518 prefixEnd_2389518 := by exact prefixLift 2389518
  have htrace : WordTrace (prefixWord ++ tailWord_2389518) baseStart_2389518 baseEnd_2389518 := by
    simpa [prefixWord, tailWord_2389518, baseEnd_2389518] using wordTrace_append hprefix tailTrace_2389518
  have hstable : (prefixWord ++ tailWord_2389518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389518).length < 2 ^ (prefixWord ++ tailWord_2389518).sum := by decide
  have hdescent : baseEnd_2389518 < baseStart_2389518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389575 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 2, 3, 2]
def baseStart_2389575 : Nat := 118140960795 + 2389575 * 2 ^ 59
def prefixEnd_2389575 : Nat := 4983230072969 + 3 ^ 40 * 2389575 * 2
def baseEnd_2389575 : Nat := 1227000534967593510523051

theorem tailTrace_2389575 : CollatzResearch.WordTrace tailWord_2389575 prefixEnd_2389575 1227000534967593510523051 := by
  unfold tailWord_2389575
  simp only [CollatzResearch.WordTrace]
  refine ⟨87154960317985356764058179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58103306878656904509372119 87154960317985356764058179)
  ·
    refine ⟨130732440476978035146087269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87154960317985356764058179 130732440476978035146087269)
    ·
      refine ⟨24512332589433381589891363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130732440476978035146087269 24512332589433381589891363)
      ·
        refine ⟨36768498884150072384837045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24512332589433381589891363 36768498884150072384837045)
        ·
          refine ⟨3447046770389069286078473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36768498884150072384837045 3447046770389069286078473)
          ·
            refine ⟨2585285077791801964558855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3447046770389069286078473 2585285077791801964558855)
            ·
              refine ⟨3877927616687702946838283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585285077791801964558855 3877927616687702946838283)
              ·
                refine ⟨5816891425031554420257425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877927616687702946838283 5816891425031554420257425)
                ·
                  refine ⟨4362668568773665815193069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5816891425031554420257425 4362668568773665815193069)
                  ·
                    refine ⟨1636000713290124680697401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4362668568773665815193069 1636000713290124680697401)
                    ·
                      refine ⟨1227000534967593510523051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1636000713290124680697401 1227000534967593510523051)
                      ·
                        rfl

theorem cell23_2389575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_2389575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389575 prefixEnd_2389575 := by exact prefixLift 2389575
  have htrace : WordTrace (prefixWord ++ tailWord_2389575) baseStart_2389575 baseEnd_2389575 := by
    simpa [prefixWord, tailWord_2389575, baseEnd_2389575] using wordTrace_append hprefix tailTrace_2389575
  have hstable : (prefixWord ++ tailWord_2389575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389575).length < 2 ^ (prefixWord ++ tailWord_2389575).sum := by decide
  have hdescent : baseEnd_2389575 < baseStart_2389575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389577 : List Nat := [1, 2, 1, 1, 2, 2, 1, 13]
def baseStart_2389577 : Nat := 118140960795 + 2389577 * 2 ^ 59
def prefixEnd_2389577 : Nat := 4983230072969 + 3 ^ 40 * 2389577 * 2
def baseEnd_2389577 : Nat := 45444502293663055655483

theorem tailTrace_2389577 : CollatzResearch.WordTrace tailWord_2389577 prefixEnd_2389577 45444502293663055655483 := by
  unfold tailWord_2389577
  simp only [CollatzResearch.WordTrace]
  refine ⟨87155033263978111105630985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58103355509318740737087323 87155033263978111105630985)
  ·
    refine ⟨65366274947983583329223239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87155033263978111105630985 65366274947983583329223239)
    ·
      refine ⟨98049412421975374993834859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65366274947983583329223239 98049412421975374993834859)
      ·
        refine ⟨147074118632963062490752289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98049412421975374993834859 147074118632963062490752289)
        ·
          refine ⟨110305588974722296868064217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147074118632963062490752289 110305588974722296868064217)
          ·
            refine ⟨82729191731041722651048163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110305588974722296868064217 82729191731041722651048163)
            ·
              refine ⟨124093787596562583976572245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82729191731041722651048163 124093787596562583976572245)
              ·
                refine ⟨45444502293663055655483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 124093787596562583976572245 45444502293663055655483)
                ·
                  rfl

theorem cell23_2389577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 13].length) (baseStart_2389577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389577 prefixEnd_2389577 := by exact prefixLift 2389577
  have htrace : WordTrace (prefixWord ++ tailWord_2389577) baseStart_2389577 baseEnd_2389577 := by
    simpa [prefixWord, tailWord_2389577, baseEnd_2389577] using wordTrace_append hprefix tailTrace_2389577
  have hstable : (prefixWord ++ tailWord_2389577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389577).length < 2 ^ (prefixWord ++ tailWord_2389577).sum := by decide
  have hdescent : baseEnd_2389577 < baseStart_2389577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389584 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 4]
def baseStart_2389584 : Nat := 118140960795 + 2389584 * 2 ^ 59
def prefixEnd_2389584 : Nat := 4983230072969 + 3 ^ 40 * 2389584 * 2
def baseEnd_2389584 : Nat := 1227005156293483975310509

theorem tailTrace_2389584 : CollatzResearch.WordTrace tailWord_2389584 prefixEnd_2389584 1227005156293483975310509 := by
  unfold tailWord_2389584
  simp only [CollatzResearch.WordTrace]
  refine ⟨43577644287476375650567903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58103525716635167534090537 43577644287476375650567903)
  ·
    refine ⟨65366466431214563475851855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43577644287476375650567903 65366466431214563475851855)
    ·
      refine ⟨98049699646821845213777783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65366466431214563475851855 98049699646821845213777783)
      ·
        refine ⟨147074549470232767820666675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98049699646821845213777783 147074549470232767820666675)
        ·
          refine ⟨220611824205349151731000013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147074549470232767820666675 220611824205349151731000013)
          ·
            refine ⟨82729434077005931899125005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220611824205349151731000013 82729434077005931899125005)
            ·
              refine ⟨31023537778877224462171877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82729434077005931899125005 31023537778877224462171877)
              ·
                refine ⟨5816913333539479586657227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31023537778877224462171877 5816913333539479586657227)
                ·
                  refine ⟨8725370000309219379985841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5816913333539479586657227 8725370000309219379985841)
                  ·
                    refine ⟨6544027500231914534989381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8725370000309219379985841 6544027500231914534989381)
                    ·
                      refine ⟨1227005156293483975310509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6544027500231914534989381 1227005156293483975310509)
                      ·
                        rfl

theorem cell23_2389584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_2389584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389584 prefixEnd_2389584 := by exact prefixLift 2389584
  have htrace : WordTrace (prefixWord ++ tailWord_2389584) baseStart_2389584 baseEnd_2389584 := by
    simpa [prefixWord, tailWord_2389584, baseEnd_2389584] using wordTrace_append hprefix tailTrace_2389584
  have hstable : (prefixWord ++ tailWord_2389584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389584).length < 2 ^ (prefixWord ++ tailWord_2389584).sum := by decide
  have hdescent : baseEnd_2389584 < baseStart_2389584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389588 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_2389588 : Nat := 118140960795 + 2389588 * 2 ^ 59
def prefixEnd_2389588 : Nat := 4983230072969 + 3 ^ 40 * 2389588 * 2
def baseEnd_2389588 : Nat := 1227007210216101959660491

theorem tailTrace_2389588 : CollatzResearch.WordTrace tailWord_2389588 prefixEnd_2389588 1227007210216101959660491 := by
  unfold tailWord_2389588
  simp only [CollatzResearch.WordTrace]
  refine ⟨43577717233469129992140709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58103622977958839989520945 43577717233469129992140709)
  ·
    refine ⟨8170821981275461873526383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43577717233469129992140709 8170821981275461873526383)
    ·
      refine ⟨12256232971913192810289575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8170821981275461873526383 12256232971913192810289575)
      ·
        refine ⟨18384349457869789215434363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12256232971913192810289575 18384349457869789215434363)
        ·
          refine ⟨27576524186804683823151545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18384349457869789215434363 27576524186804683823151545)
          ·
            refine ⟨20682393140103512867363659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27576524186804683823151545 20682393140103512867363659)
            ·
              refine ⟨31023589710155269301045489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20682393140103512867363659 31023589710155269301045489)
              ·
                refine ⟨23267692282616451975784117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31023589710155269301045489 23267692282616451975784117)
                ·
                  refine ⟨2181346151495292372729761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23267692282616451975784117 2181346151495292372729761)
                  ·
                    refine ⟨1636009613621469279547321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2181346151495292372729761 1636009613621469279547321)
                    ·
                      refine ⟨1227007210216101959660491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1636009613621469279547321 1227007210216101959660491)
                      ·
                        rfl

theorem cell23_2389588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_2389588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389588 prefixEnd_2389588 := by exact prefixLift 2389588
  have htrace : WordTrace (prefixWord ++ tailWord_2389588) baseStart_2389588 baseEnd_2389588 := by
    simpa [prefixWord, tailWord_2389588, baseEnd_2389588] using wordTrace_append hprefix tailTrace_2389588
  have hstable : (prefixWord ++ tailWord_2389588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389588).length < 2 ^ (prefixWord ++ tailWord_2389588).sum := by decide
  have hdescent : baseEnd_2389588 < baseStart_2389588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389605 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 3, 2, 2]
def baseStart_2389605 : Nat := 118140960795 + 2389605 * 2 ^ 59
def prefixEnd_2389605 : Nat := 4983230072969 + 3 ^ 40 * 2389605 * 2
def baseEnd_2389605 : Nat := 1227015939387228393147913

theorem tailTrace_2389605 : CollatzResearch.WordTrace tailWord_2389605 prefixEnd_2389605 1227015939387228393147913 := by
  unfold tailWord_2389605
  simp only [CollatzResearch.WordTrace]
  refine ⟨87156054507876671887650269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58104036338584447925100179 87156054507876671887650269)
  ·
    refine ⟨32683520440453751957868851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87156054507876671887650269 32683520440453751957868851)
    ·
      refine ⟨49025280660680627936803277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32683520440453751957868851 49025280660680627936803277)
      ·
        refine ⟨18384480247755235476301229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49025280660680627936803277 18384480247755235476301229)
        ·
          refine ⟨6894180092908213303612961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18384480247755235476301229 6894180092908213303612961)
          ·
            refine ⟨5170635069681159977709721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6894180092908213303612961 5170635069681159977709721)
            ·
              refine ⟨3877976302260869983282291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5170635069681159977709721 3877976302260869983282291)
              ·
                refine ⟨5816964453391304974923437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877976302260869983282291 5816964453391304974923437)
                ·
                  refine ⟨2181361670021739365596289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5816964453391304974923437 2181361670021739365596289)
                  ·
                    refine ⟨1636021252516304524197217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2181361670021739365596289 1636021252516304524197217)
                    ·
                      refine ⟨1227015939387228393147913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1636021252516304524197217 1227015939387228393147913)
                      ·
                        rfl

theorem cell23_2389605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_2389605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389605 prefixEnd_2389605 := by exact prefixLift 2389605
  have htrace : WordTrace (prefixWord ++ tailWord_2389605) baseStart_2389605 baseEnd_2389605 := by
    simpa [prefixWord, tailWord_2389605, baseEnd_2389605] using wordTrace_append hprefix tailTrace_2389605
  have hstable : (prefixWord ++ tailWord_2389605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389605).length < 2 ^ (prefixWord ++ tailWord_2389605).sum := by decide
  have hdescent : baseEnd_2389605 < baseStart_2389605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389618 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_2389618 : Nat := 118140960795 + 2389618 * 2 ^ 59
def prefixEnd_2389618 : Nat := 4983230072969 + 3 ^ 40 * 2389618 * 2
def baseEnd_2389618 : Nat := 1227022614635736842285353

theorem tailTrace_2389618 : CollatzResearch.WordTrace tailWord_2389618 prefixEnd_2389618 1227022614635736842285353 := by
  unfold tailWord_2389618
  simp only [CollatzResearch.WordTrace]
  refine ⟨21789132164207393776968377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58104352437886383405249005 21789132164207393776968377)
  ·
    refine ⟨16341849123155545332726283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21789132164207393776968377 16341849123155545332726283)
    ·
      refine ⟨24512773684733317999089425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16341849123155545332726283 24512773684733317999089425)
      ·
        refine ⟨18384580263549988499317069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24512773684733317999089425 18384580263549988499317069)
        ·
          refine ⟨6894217598831245687243901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18384580263549988499317069 6894217598831245687243901)
          ·
            refine ⟨2585331599561717132716463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6894217598831245687243901 2585331599561717132716463)
            ·
              refine ⟨3877997399342575699074695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585331599561717132716463 3877997399342575699074695)
              ·
                refine ⟨5816996099013863548612043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877997399342575699074695 5816996099013863548612043)
                ·
                  refine ⟨8725494148520795322918065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5816996099013863548612043 8725494148520795322918065)
                  ·
                    refine ⟨6544120611390596492188549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8725494148520795322918065 6544120611390596492188549)
                    ·
                      refine ⟨1227022614635736842285353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6544120611390596492188549 1227022614635736842285353)
                      ·
                        rfl

theorem cell23_2389618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_2389618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389618 prefixEnd_2389618 := by exact prefixLift 2389618
  have htrace : WordTrace (prefixWord ++ tailWord_2389618) baseStart_2389618 baseEnd_2389618 := by
    simpa [prefixWord, tailWord_2389618, baseEnd_2389618] using wordTrace_append hprefix tailTrace_2389618
  have hstable : (prefixWord ++ tailWord_2389618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389618).length < 2 ^ (prefixWord ++ tailWord_2389618).sum := by decide
  have hdescent : baseEnd_2389618 < baseStart_2389618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389631 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 7, 3, 2]
def baseStart_2389631 : Nat := 118140960795 + 2389631 * 2 ^ 59
def prefixEnd_2389631 : Nat := 4983230072969 + 3 ^ 40 * 2389631 * 2
def baseEnd_2389631 : Nat := 1227029289884245291422793

theorem tailTrace_2389631 : CollatzResearch.WordTrace tailWord_2389631 prefixEnd_2389631 1227029289884245291422793 := by
  unfold tailWord_2389631
  simp only [CollatzResearch.WordTrace]
  refine ⟨87157002805782478328096747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58104668537188318885397831 87157002805782478328096747)
  ·
    refine ⟨130735504208673717492145121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87157002805782478328096747 130735504208673717492145121)
    ·
      refine ⟨98051628156505288119108841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130735504208673717492145121 98051628156505288119108841)
      ·
        refine ⟨73538721117378966089331631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98051628156505288119108841 73538721117378966089331631)
        ·
          refine ⟨110308081676068449133997447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73538721117378966089331631 110308081676068449133997447)
          ·
            refine ⟨165462122514102673700996171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110308081676068449133997447 165462122514102673700996171)
            ·
              refine ⟨248193183771154010551494257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165462122514102673700996171 248193183771154010551494257)
              ·
                refine ⟨186144887828365507913620693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248193183771154010551494257 186144887828365507913620693)
                ·
                  refine ⟨4362770808477316591725485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 186144887828365507913620693 4362770808477316591725485)
                  ·
                    refine ⟨1636039053178993721897057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4362770808477316591725485 1636039053178993721897057)
                    ·
                      refine ⟨1227029289884245291422793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1636039053178993721897057 1227029289884245291422793)
                      ·
                        rfl

theorem cell23_2389631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 3, 2].length) (baseStart_2389631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389631 prefixEnd_2389631 := by exact prefixLift 2389631
  have htrace : WordTrace (prefixWord ++ tailWord_2389631) baseStart_2389631 baseEnd_2389631 := by
    simpa [prefixWord, tailWord_2389631, baseEnd_2389631] using wordTrace_append hprefix tailTrace_2389631
  have hstable : (prefixWord ++ tailWord_2389631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389631).length < 2 ^ (prefixWord ++ tailWord_2389631).sum := by decide
  have hdescent : baseEnd_2389631 < baseStart_2389631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389725 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2389725 : Nat := 118140960795 + 2389725 * 2 ^ 59
def prefixEnd_2389725 : Nat := 4983230072969 + 3 ^ 40 * 2389725 * 2
def baseEnd_2389725 : Nat := 1227077557065767923647361

theorem tailTrace_2389725 : CollatzResearch.WordTrace tailWord_2389725 prefixEnd_2389725 1227077557065767923647361 := by
  unfold tailWord_2389725
  simp only [CollatzResearch.WordTrace]
  refine ⟨87160431267441932382018629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58106954178294621588012419 87160431267441932382018629)
  ·
    refine ⟨16342580862645362321628493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87160431267441932382018629 16342580862645362321628493)
    ·
      refine ⟨6128467823492010870610685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16342580862645362321628493 6128467823492010870610685)
      ·
        refine ⟨2298175433809504076479007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6128467823492010870610685 2298175433809504076479007)
        ·
          refine ⟨3447263150714256114718511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2298175433809504076479007 3447263150714256114718511)
          ·
            refine ⟨5170894726071384172077767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3447263150714256114718511 5170894726071384172077767)
            ·
              refine ⟨7756342089107076258116651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5170894726071384172077767 7756342089107076258116651)
              ·
                refine ⟨11634513133660614387174977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7756342089107076258116651 11634513133660614387174977)
                ·
                  refine ⟨8725884850245460790381233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11634513133660614387174977 8725884850245460790381233)
                  ·
                    refine ⟨6544413637684095592785925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8725884850245460790381233 6544413637684095592785925)
                    ·
                      refine ⟨1227077557065767923647361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6544413637684095592785925 1227077557065767923647361)
                      ·
                        rfl

theorem cell23_2389725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2389725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389725 prefixEnd_2389725 := by exact prefixLift 2389725
  have htrace : WordTrace (prefixWord ++ tailWord_2389725) baseStart_2389725 baseEnd_2389725 := by
    simpa [prefixWord, tailWord_2389725, baseEnd_2389725] using wordTrace_append hprefix tailTrace_2389725
  have hstable : (prefixWord ++ tailWord_2389725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389725).length < 2 ^ (prefixWord ++ tailWord_2389725).sum := by decide
  have hdescent : baseEnd_2389725 < baseStart_2389725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389744 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 1, 10]
def baseStart_2389744 : Nat := 118140960795 + 2389744 * 2 ^ 59
def prefixEnd_2389744 : Nat := 4983230072969 + 3 ^ 40 * 2389744 * 2
def baseEnd_2389744 : Nat := 409029104399401116436591

theorem tailTrace_2389744 : CollatzResearch.WordTrace tailWord_2389744 prefixEnd_2389744 409029104399401116436591 := by
  unfold tailWord_2389744
  simp only [CollatzResearch.WordTrace]
  refine ⟨43580562127186549313480143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58107416169582065751306857 43580562127186549313480143)
  ·
    refine ⟨65370843190779823970220215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43580562127186549313480143 65370843190779823970220215)
    ·
      refine ⟨98056264786169735955330323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65370843190779823970220215 98056264786169735955330323)
      ·
        refine ⟨147084397179254603932995485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98056264786169735955330323 147084397179254603932995485)
        ·
          refine ⟨55156648942220476474873307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147084397179254603932995485 55156648942220476474873307)
          ·
            refine ⟨82734973413330714712309961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55156648942220476474873307 82734973413330714712309961)
            ·
              refine ⟨62051230059998036034232471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82734973413330714712309961 62051230059998036034232471)
              ·
                refine ⟨93076845089997054051348707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62051230059998036034232471 93076845089997054051348707)
                ·
                  refine ⟨139615267634995581077023061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93076845089997054051348707 139615267634995581077023061)
                  ·
                    refine ⟨409029104399401116436591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 139615267634995581077023061 409029104399401116436591)
                    ·
                      rfl

theorem cell23_2389744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_2389744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389744 prefixEnd_2389744 := by exact prefixLift 2389744
  have htrace : WordTrace (prefixWord ++ tailWord_2389744) baseStart_2389744 baseEnd_2389744 := by
    simpa [prefixWord, tailWord_2389744, baseEnd_2389744] using wordTrace_append hprefix tailTrace_2389744
  have hstable : (prefixWord ++ tailWord_2389744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389744).length < 2 ^ (prefixWord ++ tailWord_2389744).sum := by decide
  have hdescent : baseEnd_2389744 < baseStart_2389744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389768 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 4, 4, 2]
def baseStart_2389768 : Nat := 118140960795 + 2389768 * 2 ^ 59
def prefixEnd_2389768 : Nat := 4983230072969 + 3 ^ 40 * 2389768 * 2
def baseEnd_2389768 : Nat := 1227099636733911255409663

theorem tailTrace_2389768 : CollatzResearch.WordTrace tailWord_2389768 prefixEnd_2389768 1227099636733911255409663 := by
  unfold tailWord_2389768
  simp only [CollatzResearch.WordTrace]
  refine ⟨43580999803143075362916979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58107999737524100483889305 43580999803143075362916979)
  ·
    refine ⟨65371499704714613044375469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43580999803143075362916979 65371499704714613044375469)
    ·
      refine ⟨24514312389267979891640801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65371499704714613044375469 24514312389267979891640801)
      ·
        refine ⟨18385734291950984918730601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24514312389267979891640801 18385734291950984918730601)
        ·
          refine ⟨13789300718963238689047951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18385734291950984918730601 13789300718963238689047951)
          ·
            refine ⟨20683951078444858033571927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13789300718963238689047951 20683951078444858033571927)
            ·
              refine ⟨31025926617667287050357891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20683951078444858033571927 31025926617667287050357891)
              ·
                refine ⟨46538889926500930575536837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31025926617667287050357891 46538889926500930575536837)
                ·
                  refine ⟨8726041861218924482913157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46538889926500930575536837 8726041861218924482913157)
                  ·
                    refine ⟨1636132848978548340546217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8726041861218924482913157 1636132848978548340546217)
                    ·
                      refine ⟨1227099636733911255409663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1636132848978548340546217 1227099636733911255409663)
                      ·
                        rfl

theorem cell23_2389768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_2389768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389768 prefixEnd_2389768 := by exact prefixLift 2389768
  have htrace : WordTrace (prefixWord ++ tailWord_2389768) baseStart_2389768 baseEnd_2389768 := by
    simpa [prefixWord, tailWord_2389768, baseEnd_2389768] using wordTrace_append hprefix tailTrace_2389768
  have hstable : (prefixWord ++ tailWord_2389768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389768).length < 2 ^ (prefixWord ++ tailWord_2389768).sum := by decide
  have hdescent : baseEnd_2389768 < baseStart_2389768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389855 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 1, 5]
def baseStart_2389855 : Nat := 118140960795 + 2389855 * 2 ^ 59
def prefixEnd_2389855 : Nat := 4983230072969 + 3 ^ 40 * 2389855 * 2
def baseEnd_2389855 : Nat := 409048103183617471673921

theorem tailTrace_2389855 : CollatzResearch.WordTrace tailWord_2389855 prefixEnd_2389855 409048103183617471673921 := by
  unfold tailWord_2389855
  simp only [CollatzResearch.WordTrace]
  refine ⟨87165172756970964584251019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58110115171313976389500679 87165172756970964584251019)
  ·
    refine ⟨130747759135456446876376529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87165172756970964584251019 130747759135456446876376529)
    ·
      refine ⟨98060819351592335157282397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130747759135456446876376529 98060819351592335157282397)
      ·
        refine ⟨36772807256847125683980899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98060819351592335157282397 36772807256847125683980899)
        ·
          refine ⟨55159210885270688525971349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36772807256847125683980899 55159210885270688525971349)
          ·
            refine ⟨2585588010247063524654907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55159210885270688525971349 2585588010247063524654907)
            ·
              refine ⟨3878382015370595286982361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585588010247063524654907 3878382015370595286982361)
              ·
                refine ⟨2908786511527946465236771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3878382015370595286982361 2908786511527946465236771)
                ·
                  refine ⟨4363179767291919697855157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908786511527946465236771 4363179767291919697855157)
                  ·
                    refine ⟨409048103183617471673921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4363179767291919697855157 409048103183617471673921)
                    ·
                      rfl

theorem cell23_2389855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 5].length) (baseStart_2389855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389855 prefixEnd_2389855 := by exact prefixLift 2389855
  have htrace : WordTrace (prefixWord ++ tailWord_2389855) baseStart_2389855 baseEnd_2389855 := by
    simpa [prefixWord, tailWord_2389855, baseEnd_2389855] using wordTrace_append hprefix tailTrace_2389855
  have hstable : (prefixWord ++ tailWord_2389855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389855).length < 2 ^ (prefixWord ++ tailWord_2389855).sum := by decide
  have hdescent : baseEnd_2389855 < baseStart_2389855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389868 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_2389868 : Nat := 118140960795 + 2389868 * 2 ^ 59
def prefixEnd_2389868 : Nat := 4983230072969 + 3 ^ 40 * 2389868 * 2
def baseEnd_2389868 : Nat := 409050328266453621386401

theorem tailTrace_2389868 : CollatzResearch.WordTrace tailWord_2389868 prefixEnd_2389868 409050328266453621386401 := by
  unfold tailWord_2389868
  simp only [CollatzResearch.WordTrace]
  refine ⟨43582823452961933902237129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58110431270615911869649505 43582823452961933902237129)
  ·
    refine ⟨32687117589721450426677847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43582823452961933902237129 32687117589721450426677847)
    ·
      refine ⟨49030676384582175640016771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32687117589721450426677847 49030676384582175640016771)
      ·
        refine ⟨73546014576873263460025157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49030676384582175640016771 73546014576873263460025157)
        ·
          refine ⟨13789877733163736898754717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73546014576873263460025157 13789877733163736898754717)
          ·
            refine ⟨5171204149936401337033019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13789877733163736898754717 5171204149936401337033019)
            ·
              refine ⟨7756806224904602005549529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5171204149936401337033019 7756806224904602005549529)
              ·
                refine ⟨5817604668678451504162147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7756806224904602005549529 5817604668678451504162147)
                ·
                  refine ⟨8726407003017677256243221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5817604668678451504162147 8726407003017677256243221)
                  ·
                    refine ⟨409050328266453621386401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8726407003017677256243221 409050328266453621386401)
                    ·
                      rfl

theorem cell23_2389868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_2389868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389868 prefixEnd_2389868 := by exact prefixLift 2389868
  have htrace : WordTrace (prefixWord ++ tailWord_2389868) baseStart_2389868 baseEnd_2389868 := by
    simpa [prefixWord, tailWord_2389868, baseEnd_2389868] using wordTrace_append hprefix tailTrace_2389868
  have hstable : (prefixWord ++ tailWord_2389868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389868).length < 2 ^ (prefixWord ++ tailWord_2389868).sum := by decide
  have hdescent : baseEnd_2389868 < baseStart_2389868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389886 : List Nat := [4, 2, 3, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2389886 : Nat := 118140960795 + 2389886 * 2 ^ 59
def prefixEnd_2389886 : Nat := 4983230072969 + 3 ^ 40 * 2389886 * 2
def baseEnd_2389886 : Nat := 1227160227451141793734121

theorem tailTrace_2389886 : CollatzResearch.WordTrace tailWord_2389886 prefixEnd_2389886 1227160227451141793734121 := by
  unfold tailWord_2389886
  simp only [CollatzResearch.WordTrace]
  refine ⟨10895787927482332109828689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58110868946572437919086341 10895787927482332109828689)
  ·
    refine ⟨8171840945611749082371517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10895787927482332109828689 8171840945611749082371517)
    ·
      refine ⟨3064440354604405905889319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8171840945611749082371517 3064440354604405905889319)
      ·
        refine ⟨4596660531906608858833979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3064440354604405905889319 4596660531906608858833979)
        ·
          refine ⟨6894990797859913288250969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4596660531906608858833979 6894990797859913288250969)
          ·
            refine ⟨5171243098394934966188227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6894990797859913288250969 5171243098394934966188227)
            ·
              refine ⟨7756864647592402449282341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5171243098394934966188227 7756864647592402449282341)
              ·
                refine ⟨1454412121423575459240439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7756864647592402449282341 1454412121423575459240439)
                ·
                  refine ⟨2181618182135363188860659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1454412121423575459240439 2181618182135363188860659)
                  ·
                    refine ⟨3272427273203044783290989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2181618182135363188860659 3272427273203044783290989)
                    ·
                      refine ⟨1227160227451141793734121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3272427273203044783290989 1227160227451141793734121)
                      ·
                        rfl

theorem cell23_2389886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2389886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389886 prefixEnd_2389886 := by exact prefixLift 2389886
  have htrace : WordTrace (prefixWord ++ tailWord_2389886) baseStart_2389886 baseEnd_2389886 := by
    simpa [prefixWord, tailWord_2389886, baseEnd_2389886] using wordTrace_append hprefix tailTrace_2389886
  have hstable : (prefixWord ++ tailWord_2389886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389886).length < 2 ^ (prefixWord ++ tailWord_2389886).sum := by decide
  have hdescent : baseEnd_2389886 < baseStart_2389886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389902 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_2389902 : Nat := 118140960795 + 2389902 * 2 ^ 59
def prefixEnd_2389902 : Nat := 4983230072969 + 3 ^ 40 * 2389902 * 2
def baseEnd_2389902 : Nat := 409056147713871243711349

theorem tailTrace_2389902 : CollatzResearch.WordTrace tailWord_2389902 prefixEnd_2389902 409056147713871243711349 := by
  unfold tailWord_2389902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10895860873475086451401495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58111257991867127740807973 10895860873475086451401495)
  ·
    refine ⟨16343791310212629677102243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10895860873475086451401495 16343791310212629677102243)
    ·
      refine ⟨24515686965318944515653365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16343791310212629677102243 24515686965318944515653365)
      ·
        refine ⟨2298345652998651048342503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24515686965318944515653365 2298345652998651048342503)
        ·
          refine ⟨3447518479497976572513755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2298345652998651048342503 3447518479497976572513755)
          ·
            refine ⟨5171277719246964858770633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3447518479497976572513755 5171277719246964858770633)
            ·
              refine ⟨3878458289435223644077975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5171277719246964858770633 3878458289435223644077975)
              ·
                refine ⟨5817687434152835466116963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3878458289435223644077975 5817687434152835466116963)
                ·
                  refine ⟨8726531151229253199175445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5817687434152835466116963 8726531151229253199175445)
                  ·
                    refine ⟨409056147713871243711349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8726531151229253199175445 409056147713871243711349)
                    ·
                      rfl

theorem cell23_2389902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_2389902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389902 prefixEnd_2389902 := by exact prefixLift 2389902
  have htrace : WordTrace (prefixWord ++ tailWord_2389902) baseStart_2389902 baseEnd_2389902 := by
    simpa [prefixWord, tailWord_2389902, baseEnd_2389902] using wordTrace_append hprefix tailTrace_2389902
  have hstable : (prefixWord ++ tailWord_2389902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389902).length < 2 ^ (prefixWord ++ tailWord_2389902).sum := by decide
  have hdescent : baseEnd_2389902 < baseStart_2389902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389968 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 3]
def baseStart_2389968 : Nat := 118140960795 + 2389968 * 2 ^ 59
def prefixEnd_2389968 : Nat := 4983230072969 + 3 ^ 40 * 2389968 * 2
def baseEnd_2389968 : Nat := 1227202332864810472908743

theorem tailTrace_2389968 : CollatzResearch.WordTrace tailWord_2389968 prefixEnd_2389968 1227202332864810472908743 := by
  unfold tailWord_2389968
  simp only [CollatzResearch.WordTrace]
  refine ⟨43584647102780792441557279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58112862803707723255409705 43584647102780792441557279)
  ·
    refine ⟨65376970654171188662335919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43584647102780792441557279 65376970654171188662335919)
    ·
      refine ⟨98065455981256782993503879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65376970654171188662335919 98065455981256782993503879)
      ·
        refine ⟨147098183971885174490255819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98065455981256782993503879 147098183971885174490255819)
        ·
          refine ⟨220647275957827761735383729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147098183971885174490255819 220647275957827761735383729)
          ·
            refine ⟨165485456968370821301537797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220647275957827761735383729 165485456968370821301537797)
            ·
              refine ⟨31028523181569528994038337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165485456968370821301537797 31028523181569528994038337)
              ·
                refine ⟨23271392386177146745528753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31028523181569528994038337 23271392386177146745528753)
                ·
                  refine ⟨17453544289632860059146565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23271392386177146745528753 17453544289632860059146565)
                  ·
                    refine ⟨3272539554306161261089981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17453544289632860059146565 3272539554306161261089981)
                    ·
                      refine ⟨1227202332864810472908743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3272539554306161261089981 1227202332864810472908743)
                      ·
                        rfl

theorem cell23_2389968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 3].length) (baseStart_2389968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2389968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2389968 prefixEnd_2389968 := by exact prefixLift 2389968
  have htrace : WordTrace (prefixWord ++ tailWord_2389968) baseStart_2389968 baseEnd_2389968 := by
    simpa [prefixWord, tailWord_2389968, baseEnd_2389968] using wordTrace_append hprefix tailTrace_2389968
  have hstable : (prefixWord ++ tailWord_2389968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389968).length < 2 ^ (prefixWord ++ tailWord_2389968).sum := by decide
  have hdescent : baseEnd_2389968 < baseStart_2389968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390028 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2390028 : Nat := 118140960795 + 2390028 * 2 ^ 59
def prefixEnd_2390028 : Nat := 4983230072969 + 3 ^ 40 * 2390028 * 2
def baseEnd_2390028 : Nat := 1227233141704080238158467

theorem tailTrace_2390028 : CollatzResearch.WordTrace tailWord_2390028 prefixEnd_2390028 1227233141704080238158467 := by
  unfold tailWord_2390028
  simp only [CollatzResearch.WordTrace]
  refine ⟨43585741292672107565149369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58114321723562810086865825 43585741292672107565149369)
  ·
    refine ⟨32689305969504080673862027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43585741292672107565149369 32689305969504080673862027)
    ·
      refine ⟨49033958954256121010793041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32689305969504080673862027 49033958954256121010793041)
      ·
        refine ⟨36775469215692090758094781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49033958954256121010793041 36775469215692090758094781)
        ·
          refine ⟨13790800955884534034285543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36775469215692090758094781 13790800955884534034285543)
          ·
            refine ⟨20686201433826801051428315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13790800955884534034285543 20686201433826801051428315)
            ·
              refine ⟨31029302150740201577142473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20686201433826801051428315 31029302150740201577142473)
              ·
                refine ⟨23271976613055151182856855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31029302150740201577142473 23271976613055151182856855)
                ·
                  refine ⟨34907964919582726774285283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23271976613055151182856855 34907964919582726774285283)
                  ·
                    refine ⟨52361947379374090161427925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34907964919582726774285283 52361947379374090161427925)
                    ·
                      refine ⟨1227233141704080238158467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52361947379374090161427925 1227233141704080238158467)
                      ·
                        rfl

theorem cell23_2390028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2390028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390028 prefixEnd_2390028 := by exact prefixLift 2390028
  have htrace : WordTrace (prefixWord ++ tailWord_2390028) baseStart_2390028 baseEnd_2390028 := by
    simpa [prefixWord, tailWord_2390028, baseEnd_2390028] using wordTrace_append hprefix tailTrace_2390028
  have hstable : (prefixWord ++ tailWord_2390028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390028).length < 2 ^ (prefixWord ++ tailWord_2390028).sum := by decide
  have hdescent : baseEnd_2390028 < baseStart_2390028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390045 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_2390045 : Nat := 118140960795 + 2390045 * 2 ^ 59
def prefixEnd_2390045 : Nat := 4983230072969 + 3 ^ 40 * 2390045 * 2
def baseEnd_2390045 : Nat := 1227241870875206671645889

theorem tailTrace_2390045 : CollatzResearch.WordTrace tailWord_2390045 prefixEnd_2390045 1227241870875206671645889 := by
  unfold tailWord_2390045
  simp only [CollatzResearch.WordTrace]
  refine ⟨87172102626282627033667589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58114735084188418022445059 87172102626282627033667589)
  ·
    refine ⟨16344769242427992568812673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87172102626282627033667589 16344769242427992568812673)
    ·
      refine ⟨12258576931820994426609505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16344769242427992568812673 12258576931820994426609505)
      ·
        refine ⟨9193932698865745819957129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12258576931820994426609505 9193932698865745819957129)
        ·
          refine ⟨6895449524149309364967847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9193932698865745819957129 6895449524149309364967847)
          ·
            refine ⟨10343174286223964047451771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6895449524149309364967847 10343174286223964047451771)
            ·
              refine ⟨15514761429335946071177657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10343174286223964047451771 15514761429335946071177657)
              ·
                refine ⟨11636071072001959553383243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15514761429335946071177657 11636071072001959553383243)
                ·
                  refine ⟨17454106608002939330074865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11636071072001959553383243 17454106608002939330074865)
                  ·
                    refine ⟨13090579956002204497556149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17454106608002939330074865 13090579956002204497556149)
                    ·
                      refine ⟨1227241870875206671645889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13090579956002204497556149 1227241870875206671645889)
                      ·
                        rfl

theorem cell23_2390045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_2390045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390045 prefixEnd_2390045 := by exact prefixLift 2390045
  have htrace : WordTrace (prefixWord ++ tailWord_2390045) baseStart_2390045 baseEnd_2390045 := by
    simpa [prefixWord, tailWord_2390045, baseEnd_2390045] using wordTrace_append hprefix tailTrace_2390045
  have hstable : (prefixWord ++ tailWord_2390045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390045).length < 2 ^ (prefixWord ++ tailWord_2390045).sum := by decide
  have hdescent : baseEnd_2390045 < baseStart_2390045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390092 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2390092 : Nat := 118140960795 + 2390092 * 2 ^ 59
def prefixEnd_2390092 : Nat := 4983230072969 + 3 ^ 40 * 2390092 * 2
def baseEnd_2390092 : Nat := 1227266004465967987758173

theorem tailTrace_2390092 : CollatzResearch.WordTrace tailWord_2390092 prefixEnd_2390092 1227266004465967987758173 := by
  unfold tailWord_2390092
  simp only [CollatzResearch.WordTrace]
  refine ⟨43586908428556177030314265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58115877904741569373752353 43586908428556177030314265)
  ·
    refine ⟨32690181321417132772735699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43586908428556177030314265 32690181321417132772735699)
    ·
      refine ⟨49035271982125699159103549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32690181321417132772735699 49035271982125699159103549)
      ·
        refine ⟨18388226993297137184663831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49035271982125699159103549 18388226993297137184663831)
        ·
          refine ⟨27582340489945705776995747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18388226993297137184663831 27582340489945705776995747)
          ·
            refine ⟨41373510734918558665493621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27582340489945705776995747 41373510734918558665493621)
            ·
              refine ⟨3878766631398614874890027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41373510734918558665493621 3878766631398614874890027)
              ·
                refine ⟨5818149947097922312335041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3878766631398614874890027 5818149947097922312335041)
                ·
                  refine ⟨4363612460323441734251281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5818149947097922312335041 4363612460323441734251281)
                  ·
                    refine ⟨3272709345242581300688461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4363612460323441734251281 3272709345242581300688461)
                    ·
                      refine ⟨1227266004465967987758173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3272709345242581300688461 1227266004465967987758173)
                      ·
                        rfl

theorem cell23_2390092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2390092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390092 prefixEnd_2390092 := by exact prefixLift 2390092
  have htrace : WordTrace (prefixWord ++ tailWord_2390092) baseStart_2390092 baseEnd_2390092 := by
    simpa [prefixWord, tailWord_2390092, baseEnd_2390092] using wordTrace_append hprefix tailTrace_2390092
  have hstable : (prefixWord ++ tailWord_2390092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390092).length < 2 ^ (prefixWord ++ tailWord_2390092).sum := by decide
  have hdescent : baseEnd_2390092 < baseStart_2390092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390112 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 6]
def baseStart_2390112 : Nat := 118140960795 + 2390112 * 2 ^ 59
def prefixEnd_2390112 : Nat := 4983230072969 + 3 ^ 40 * 2390112 * 2
def baseEnd_2390112 : Nat := 136364030453228656612009

theorem tailTrace_2390112 : CollatzResearch.WordTrace tailWord_2390112 prefixEnd_2390112 136364030453228656612009 := by
  unfold tailWord_2390112
  simp only [CollatzResearch.WordTrace]
  refine ⟨43587273158519948738178295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58116364211359931650904393 43587273158519948738178295)
  ·
    refine ⟨65380909737779923107267443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43587273158519948738178295 65380909737779923107267443)
    ·
      refine ⟨98071364606669884660901165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65380909737779923107267443 98071364606669884660901165)
      ·
        refine ⟨36776761727501206747837937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98071364606669884660901165 36776761727501206747837937)
        ·
          refine ⟨27582571295625905060878453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36776761727501206747837937 27582571295625905060878453)
          ·
            refine ⟨2585866058964928599457355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27582571295625905060878453 2585866058964928599457355)
            ·
              refine ⟨3878799088447392899186033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585866058964928599457355 3878799088447392899186033)
              ·
                refine ⟨2909099316335544674389525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3878799088447392899186033 2909099316335544674389525)
                ·
                  refine ⟨136364030453228656612009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2909099316335544674389525 136364030453228656612009)
                  ·
                    rfl

theorem cell23_2390112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 6].length) (baseStart_2390112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390112 prefixEnd_2390112 := by exact prefixLift 2390112
  have htrace : WordTrace (prefixWord ++ tailWord_2390112) baseStart_2390112 baseEnd_2390112 := by
    simpa [prefixWord, tailWord_2390112, baseEnd_2390112] using wordTrace_append hprefix tailTrace_2390112
  have hstable : (prefixWord ++ tailWord_2390112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390112).length < 2 ^ (prefixWord ++ tailWord_2390112).sum := by decide
  have hdescent : baseEnd_2390112 < baseStart_2390112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390172 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 4, 4]
def baseStart_2390172 : Nat := 118140960795 + 2390172 * 2 ^ 59
def prefixEnd_2390172 : Nat := 4983230072969 + 3 ^ 40 * 2390172 * 2
def baseEnd_2390172 : Nat := 409102360972775891585935

theorem tailTrace_2390172 : CollatzResearch.WordTrace tailWord_2390172 prefixEnd_2390172 409102360972775891585935 := by
  unfold tailWord_2390172
  simp only [CollatzResearch.WordTrace]
  refine ⟨43588367348411263861770385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58117823131215018482360513 43588367348411263861770385)
  ·
    refine ⟨32691275511308447896327789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43588367348411263861770385 32691275511308447896327789)
    ·
      refine ⟨12259228316740667961122921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32691275511308447896327789 12259228316740667961122921)
      ·
        refine ⟨9194421237555500970842191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12259228316740667961122921 9194421237555500970842191)
        ·
          refine ⟨13791631856333251456263287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9194421237555500970842191 13791631856333251456263287)
          ·
            refine ⟨20687447784499877184394931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13791631856333251456263287 20687447784499877184394931)
            ·
              refine ⟨31031171676749815776592397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20687447784499877184394931 31031171676749815776592397)
              ·
                refine ⟨11636689378781180916222149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31031171676749815776592397 11636689378781180916222149)
                ·
                  refine ⟨2181879258521471421791653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11636689378781180916222149 2181879258521471421791653)
                  ·
                    refine ⟨409102360972775891585935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2181879258521471421791653 409102360972775891585935)
                    ·
                      rfl

theorem cell23_2390172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_2390172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390172 prefixEnd_2390172 := by exact prefixLift 2390172
  have htrace : WordTrace (prefixWord ++ tailWord_2390172) baseStart_2390172 baseEnd_2390172 := by
    simpa [prefixWord, tailWord_2390172, baseEnd_2390172] using wordTrace_append hprefix tailTrace_2390172
  have hstable : (prefixWord ++ tailWord_2390172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390172).length < 2 ^ (prefixWord ++ tailWord_2390172).sum := by decide
  have hdescent : baseEnd_2390172 < baseStart_2390172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390173 : List Nat := [1, 4, 2, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_2390173 : Nat := 118140960795 + 2390173 * 2 ^ 59
def prefixEnd_2390173 : Nat := 4983230072969 + 3 ^ 40 * 2390173 * 2
def baseEnd_2390173 : Nat := 1227307596398982170845301

theorem tailTrace_2390173 : CollatzResearch.WordTrace tailWord_2390173 prefixEnd_2390173 1227307596398982170845301 := by
  unfold tailWord_2390173
  simp only [CollatzResearch.WordTrace]
  refine ⟨87176771169818904894327173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58117847446545936596218115 87176771169818904894327173)
  ·
    refine ⟨16345644594341044667686345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87176771169818904894327173 16345644594341044667686345)
    ·
      refine ⟨12259233445755783500764759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16345644594341044667686345 12259233445755783500764759)
      ·
        refine ⟨18388850168633675251147139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12259233445755783500764759 18388850168633675251147139)
        ·
          refine ⟨27583275252950512876720709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18388850168633675251147139 27583275252950512876720709)
          ·
            refine ⟨5171864109928221164385133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27583275252950512876720709 5171864109928221164385133)
            ·
              refine ⟨1939449041223082936644425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5171864109928221164385133 1939449041223082936644425)
              ·
                refine ⟨1454586780917312202483319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1939449041223082936644425 1454586780917312202483319)
                ·
                  refine ⟨2181880171375968303724979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1454586780917312202483319 2181880171375968303724979)
                  ·
                    refine ⟨3272820257063952455587469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2181880171375968303724979 3272820257063952455587469)
                    ·
                      refine ⟨1227307596398982170845301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3272820257063952455587469 1227307596398982170845301)
                      ·
                        rfl

theorem cell23_2390173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_2390173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390173 prefixEnd_2390173 := by exact prefixLift 2390173
  have htrace : WordTrace (prefixWord ++ tailWord_2390173) baseStart_2390173 baseEnd_2390173 := by
    simpa [prefixWord, tailWord_2390173, baseEnd_2390173] using wordTrace_append hprefix tailTrace_2390173
  have hstable : (prefixWord ++ tailWord_2390173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390173).length < 2 ^ (prefixWord ++ tailWord_2390173).sum := by decide
  have hdescent : baseEnd_2390173 < baseStart_2390173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390199 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 1, 2, 3]
def baseStart_2390199 : Nat := 118140960795 + 2390199 * 2 ^ 59
def prefixEnd_2390199 : Nat := 4983230072969 + 3 ^ 40 * 2390199 * 2
def baseEnd_2390199 : Nat := 1227320946895999069120181

theorem tailTrace_2390199 : CollatzResearch.WordTrace tailWord_2390199 prefixEnd_2390199 1227320946895999069120181 := by
  unfold tailWord_2390199
  simp only [CollatzResearch.WordTrace]
  refine ⟨87177719467724711334773651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58118479645149807556515767 87177719467724711334773651)
  ·
    refine ⟨130766579201587067002160477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87177719467724711334773651 130766579201587067002160477)
    ·
      refine ⟨49037467200595150125810179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130766579201587067002160477 49037467200595150125810179)
      ·
        refine ⟨73556200800892725188715269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49037467200595150125810179 73556200800892725188715269)
        ·
          refine ⟨13791787650167385972884113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73556200800892725188715269 13791787650167385972884113)
          ·
            refine ⟨10343840737625539479663085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13791787650167385972884113 10343840737625539479663085)
            ·
              refine ⟨3878940276609577304873657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10343840737625539479663085 3878940276609577304873657)
              ·
                refine ⟨2909205207457182978655243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3878940276609577304873657 2909205207457182978655243)
                ·
                  refine ⟨4363807811185774467982865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2909205207457182978655243 4363807811185774467982865)
                  ·
                    refine ⟨3272855858389330850987149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4363807811185774467982865 3272855858389330850987149)
                    ·
                      refine ⟨1227320946895999069120181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3272855858389330850987149 1227320946895999069120181)
                      ·
                        rfl

theorem cell23_2390199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_2390199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390199 prefixEnd_2390199 := by exact prefixLift 2390199
  have htrace : WordTrace (prefixWord ++ tailWord_2390199) baseStart_2390199 baseEnd_2390199 := by
    simpa [prefixWord, tailWord_2390199, baseEnd_2390199] using wordTrace_append hprefix tailTrace_2390199
  have hstable : (prefixWord ++ tailWord_2390199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390199).length < 2 ^ (prefixWord ++ tailWord_2390199).sum := by decide
  have hdescent : baseEnd_2390199 < baseStart_2390199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390225 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_2390225 : Nat := 118140960795 + 2390225 * 2 ^ 59
def prefixEnd_2390225 : Nat := 4983230072969 + 3 ^ 40 * 2390225 * 2
def baseEnd_2390225 : Nat := 1227334297393015967395061

theorem tailTrace_2390225 : CollatzResearch.WordTrace tailWord_2390225 prefixEnd_2390225 1227334297393015967395061 := by
  unfold tailWord_2390225
  simp only [CollatzResearch.WordTrace]
  refine ⟨87178667765630517775220129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58119111843753678516813419 87178667765630517775220129)
  ·
    refine ⟨65384000824222888331415097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87178667765630517775220129 65384000824222888331415097)
    ·
      refine ⟨49038000618167166248561323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65384000824222888331415097 49038000618167166248561323)
      ·
        refine ⟨73557000927250749372841985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49038000618167166248561323 73557000927250749372841985)
        ·
          refine ⟨55167750695438062029631489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73557000927250749372841985 55167750695438062029631489)
          ·
            refine ⟨41375813021578546522223617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55167750695438062029631489 41375813021578546522223617)
            ·
              refine ⟨31031859766183909891667713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41375813021578546522223617 31031859766183909891667713)
              ·
                refine ⟨23273894824637932418750785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31031859766183909891667713 23273894824637932418750785)
                ·
                  refine ⟨17455421118478449314063089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23273894824637932418750785 17455421118478449314063089)
                  ·
                    refine ⟨13091565838858836985547317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17455421118478449314063089 13091565838858836985547317)
                    ·
                      refine ⟨1227334297393015967395061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13091565838858836985547317 1227334297393015967395061)
                      ·
                        rfl

theorem cell23_2390225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_2390225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390225 prefixEnd_2390225 := by exact prefixLift 2390225
  have htrace : WordTrace (prefixWord ++ tailWord_2390225) baseStart_2390225 baseEnd_2390225 := by
    simpa [prefixWord, tailWord_2390225, baseEnd_2390225] using wordTrace_append hprefix tailTrace_2390225
  have hstable : (prefixWord ++ tailWord_2390225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390225).length < 2 ^ (prefixWord ++ tailWord_2390225).sum := by decide
  have hdescent : baseEnd_2390225 < baseStart_2390225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390235 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 4]
def baseStart_2390235 : Nat := 118140960795 + 2390235 * 2 ^ 59
def prefixEnd_2390235 : Nat := 4983230072969 + 3 ^ 40 * 2390235 * 2
def baseEnd_2390235 : Nat := 1227339432199560928270015

theorem tailTrace_2390235 : CollatzResearch.WordTrace tailWord_2390235 prefixEnd_2390235 1227339432199560928270015 := by
  unfold tailWord_2390235
  simp only [CollatzResearch.WordTrace]
  refine ⟨87179032495594289483084159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58119354997062859655389439 87179032495594289483084159)
  ·
    refine ⟨130768548743391434224626239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87179032495594289483084159 130768548743391434224626239)
    ·
      refine ⟨196152823115087151336939359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130768548743391434224626239 196152823115087151336939359)
      ·
        refine ⟨294229234672630727005409039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196152823115087151336939359 294229234672630727005409039)
        ·
          refine ⟨441343852008946090508113559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294229234672630727005409039 441343852008946090508113559)
          ·
            refine ⟨662015778013419135762170339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441343852008946090508113559 662015778013419135762170339)
            ·
              refine ⟨993023667020128703643255509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662015778013419135762170339 993023667020128703643255509)
              ·
                refine ⟨23273992195784266491638801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 993023667020128703643255509 23273992195784266491638801)
                ·
                  refine ⟨17455494146838199868729101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23273992195784266491638801 17455494146838199868729101)
                  ·
                    refine ⟨6545810305064324950773413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17455494146838199868729101 6545810305064324950773413)
                    ·
                      refine ⟨1227339432199560928270015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6545810305064324950773413 1227339432199560928270015)
                      ·
                        rfl

theorem cell23_2390235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 4].length) (baseStart_2390235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390235 prefixEnd_2390235 := by exact prefixLift 2390235
  have htrace : WordTrace (prefixWord ++ tailWord_2390235) baseStart_2390235 baseEnd_2390235 := by
    simpa [prefixWord, tailWord_2390235, baseEnd_2390235] using wordTrace_append hprefix tailTrace_2390235
  have hstable : (prefixWord ++ tailWord_2390235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390235).length < 2 ^ (prefixWord ++ tailWord_2390235).sum := by decide
  have hdescent : baseEnd_2390235 < baseStart_2390235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390236 : List Nat := [2, 2, 5, 2, 1, 2, 1, 8]
def baseStart_2390236 : Nat := 118140960795 + 2390236 * 2 ^ 59
def prefixEnd_2390236 : Nat := 4983230072969 + 3 ^ 40 * 2390236 * 2
def baseEnd_2390236 : Nat := 45457035025193163865093

theorem tailTrace_2390236 : CollatzResearch.WordTrace tailWord_2390236 prefixEnd_2390236 45457035025193163865093 := by
  unfold tailWord_2390236
  simp only [CollatzResearch.WordTrace]
  refine ⟨43589534484295333326935281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58119379312393777769247041 43589534484295333326935281)
  ·
    refine ⟨32692150863221499995201461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43589534484295333326935281 32692150863221499995201461)
    ·
      refine ⟨3064889143427015624550137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32692150863221499995201461 3064889143427015624550137)
      ·
        refine ⟨2298666857570261718412603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3064889143427015624550137 2298666857570261718412603)
        ·
          refine ⟨3448000286355392577618905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2298666857570261718412603 3448000286355392577618905)
          ·
            refine ⟨2586000214766544433214179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3448000286355392577618905 2586000214766544433214179)
            ·
              refine ⟨3879000322149816649821269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586000214766544433214179 3879000322149816649821269)
              ·
                refine ⟨45457035025193163865093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3879000322149816649821269 45457035025193163865093)
                ·
                  rfl

theorem cell23_2390236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 8].length) (baseStart_2390236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390236 prefixEnd_2390236 := by exact prefixLift 2390236
  have htrace : WordTrace (prefixWord ++ tailWord_2390236) baseStart_2390236 baseEnd_2390236 := by
    simpa [prefixWord, tailWord_2390236, baseEnd_2390236] using wordTrace_append hprefix tailTrace_2390236
  have hstable : (prefixWord ++ tailWord_2390236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390236).length < 2 ^ (prefixWord ++ tailWord_2390236).sum := by decide
  have hdescent : baseEnd_2390236 < baseStart_2390236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390275 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 9]
def baseStart_2390275 : Nat := 118140960795 + 2390275 * 2 ^ 59
def prefixEnd_2390275 : Nat := 4983230072969 + 3 ^ 40 * 2390275 * 2
def baseEnd_2390275 : Nat := 136373330158415641307759

theorem tailTrace_2390275 : CollatzResearch.WordTrace tailWord_2390275 prefixEnd_2390275 136373330158415641307759 := by
  unfold tailWord_2390275
  simp only [CollatzResearch.WordTrace]
  refine ⟨87180491415449376314540279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58120327610299584209693519 87180491415449376314540279)
  ·
    refine ⟨130770737123174064471810419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87180491415449376314540279 130770737123174064471810419)
    ·
      refine ⟨196156105684761096707715629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130770737123174064471810419 196156105684761096707715629)
      ·
        refine ⟨73558539631785411265393361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196156105684761096707715629 73558539631785411265393361)
        ·
          refine ⟨55168904723839058449045021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73558539631785411265393361 55168904723839058449045021)
          ·
            refine ⟨20688339271439646918391883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55168904723839058449045021 20688339271439646918391883)
            ·
              refine ⟨31032508907159470377587825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20688339271439646918391883 31032508907159470377587825)
              ·
                refine ⟨23274381680369602783190869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31032508907159470377587825 23274381680369602783190869)
                ·
                  refine ⟨136373330158415641307759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23274381680369602783190869 136373330158415641307759)
                  ·
                    rfl

theorem cell23_2390275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 9].length) (baseStart_2390275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390275 prefixEnd_2390275 := by exact prefixLift 2390275
  have htrace : WordTrace (prefixWord ++ tailWord_2390275) baseStart_2390275 baseEnd_2390275 := by
    simpa [prefixWord, tailWord_2390275, baseEnd_2390275] using wordTrace_append hprefix tailTrace_2390275
  have hstable : (prefixWord ++ tailWord_2390275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390275).length < 2 ^ (prefixWord ++ tailWord_2390275).sum := by decide
  have hdescent : baseEnd_2390275 < baseStart_2390275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390282 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2390282 : Nat := 118140960795 + 2390282 * 2 ^ 59
def prefixEnd_2390282 : Nat := 4983230072969 + 3 ^ 40 * 2390282 * 2
def baseEnd_2390282 : Nat := 1227363565790322244382299

theorem tailTrace_2390282 : CollatzResearch.WordTrace tailWord_2390282 prefixEnd_2390282 1227363565790322244382299 := by
  unfold tailWord_2390282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21795186681606004127511275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58120497817616011006696733 21795186681606004127511275)
  ·
    refine ⟨32692780022409006191266913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21795186681606004127511275 32692780022409006191266913)
    ·
      refine ⟨24519585016806754643450185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32692780022409006191266913 24519585016806754643450185)
      ·
        refine ⟨18389688762605065982587639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24519585016806754643450185 18389688762605065982587639)
        ·
          refine ⟨27584533143907598973881459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18389688762605065982587639 27584533143907598973881459)
          ·
            refine ⟨41376799715861398460822189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27584533143907598973881459 41376799715861398460822189)
            ·
              refine ⟨15516299893448024422808321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41376799715861398460822189 15516299893448024422808321)
              ·
                refine ⟨11637224920086018317106241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15516299893448024422808321 11637224920086018317106241)
                ·
                  refine ⟨8727918690064513737829681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11637224920086018317106241 8727918690064513737829681)
                  ·
                    refine ⟨6545939017548385303372261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8727918690064513737829681 6545939017548385303372261)
                    ·
                      refine ⟨1227363565790322244382299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6545939017548385303372261 1227363565790322244382299)
                      ·
                        rfl

theorem cell23_2390282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2390282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390282 prefixEnd_2390282 := by exact prefixLift 2390282
  have htrace : WordTrace (prefixWord ++ tailWord_2390282) baseStart_2390282 baseEnd_2390282 := by
    simpa [prefixWord, tailWord_2390282, baseEnd_2390282] using wordTrace_append hprefix tailTrace_2390282
  have hstable : (prefixWord ++ tailWord_2390282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390282).length < 2 ^ (prefixWord ++ tailWord_2390282).sum := by decide
  have hdescent : baseEnd_2390282 < baseStart_2390282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390286 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2]
def baseStart_2390286 : Nat := 118140960795 + 2390286 * 2 ^ 59
def prefixEnd_2390286 : Nat := 4983230072969 + 3 ^ 40 * 2390286 * 2
def baseEnd_2390286 : Nat := 1227365619712940228732281

theorem tailTrace_2390286 : CollatzResearch.WordTrace tailWord_2390286 prefixEnd_2390286 1227365619712940228732281 := by
  unfold tailWord_2390286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10897611577301190649148839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58120595078939683462127141 10897611577301190649148839)
  ·
    refine ⟨16346417365951785973723259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10897611577301190649148839 16346417365951785973723259)
    ·
      refine ⟨24519626048927678960584889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16346417365951785973723259 24519626048927678960584889)
      ·
        refine ⟨18389719536695759220438667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24519626048927678960584889 18389719536695759220438667)
        ·
          refine ⟨27584579305043638830658001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18389719536695759220438667 27584579305043638830658001)
          ·
            refine ⟨20688434478782729122993501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27584579305043638830658001 20688434478782729122993501)
            ·
              refine ⟨7758162929543523421122563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20688434478782729122993501 7758162929543523421122563)
              ·
                refine ⟨11637244394315285131683845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7758162929543523421122563 11637244394315285131683845)
                ·
                  refine ⟨2181983323934115962190721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11637244394315285131683845 2181983323934115962190721)
                  ·
                    refine ⟨1636487492950586971643041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2181983323934115962190721 1636487492950586971643041)
                    ·
                      refine ⟨1227365619712940228732281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1636487492950586971643041 1227365619712940228732281)
                      ·
                        rfl

theorem cell23_2390286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_2390286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390286 prefixEnd_2390286 := by exact prefixLift 2390286
  have htrace : WordTrace (prefixWord ++ tailWord_2390286) baseStart_2390286 baseEnd_2390286 := by
    simpa [prefixWord, tailWord_2390286, baseEnd_2390286] using wordTrace_append hprefix tailTrace_2390286
  have hstable : (prefixWord ++ tailWord_2390286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390286).length < 2 ^ (prefixWord ++ tailWord_2390286).sum := by decide
  have hdescent : baseEnd_2390286 < baseStart_2390286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390332 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_2390332 : Nat := 118140960795 + 2390332 * 2 ^ 59
def prefixEnd_2390332 : Nat := 4983230072969 + 3 ^ 40 * 2390332 * 2
def baseEnd_2390332 : Nat := 1227389239823047048757069

theorem tailTrace_2390332 : CollatzResearch.WordTrace tailWord_2390332 prefixEnd_2390332 1227389239823047048757069 := by
  unfold tailWord_2390332
  simp only [CollatzResearch.WordTrace]
  refine ⟨43591285188121437524682625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58121713584161916699576833 43591285188121437524682625)
  ·
    refine ⟨32693463891091078143511969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43591285188121437524682625 32693463891091078143511969)
    ·
      refine ⟨24520097918318308607633977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32693463891091078143511969 24520097918318308607633977)
      ·
        refine ⟨18390073438738731455725483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24520097918318308607633977 18390073438738731455725483)
        ·
          refine ⟨27585110158108097183588225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18390073438738731455725483 27585110158108097183588225)
          ·
            refine ⟨20688832618581072887691169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27585110158108097183588225 20688832618581072887691169)
            ·
              refine ⟨15516624463935804665768377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20688832618581072887691169 15516624463935804665768377)
              ·
                refine ⟨11637468347951853499326283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15516624463935804665768377 11637468347951853499326283)
                ·
                  refine ⟨17456202521927780248989425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11637468347951853499326283 17456202521927780248989425)
                  ·
                    refine ⟨13092151891445835186742069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17456202521927780248989425 13092151891445835186742069)
                    ·
                      refine ⟨1227389239823047048757069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13092151891445835186742069 1227389239823047048757069)
                      ·
                        rfl

theorem cell23_2390332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_2390332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390332 prefixEnd_2390332 := by exact prefixLift 2390332
  have htrace : WordTrace (prefixWord ++ tailWord_2390332) baseStart_2390332 baseEnd_2390332 := by
    simpa [prefixWord, tailWord_2390332, baseEnd_2390332] using wordTrace_append hprefix tailTrace_2390332
  have hstable : (prefixWord ++ tailWord_2390332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390332).length < 2 ^ (prefixWord ++ tailWord_2390332).sum := by decide
  have hdescent : baseEnd_2390332 < baseStart_2390332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390359 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 1, 6, 2]
def baseStart_2390359 : Nat := 118140960795 + 2390359 * 2 ^ 59
def prefixEnd_2390359 : Nat := 4983230072969 + 3 ^ 40 * 2390359 * 2
def baseEnd_2390359 : Nat := 1227403103800718443119445

theorem tailTrace_2390359 : CollatzResearch.WordTrace tailWord_2390359 prefixEnd_2390359 1227403103800718443119445 := by
  unfold tailWord_2390359
  simp only [CollatzResearch.WordTrace]
  refine ⟨87183555147145058660598131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58122370098096705773732087 87183555147145058660598131)
  ·
    refine ⟨130775332720717587990897197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87183555147145058660598131 130775332720717587990897197)
    ·
      refine ⟨49040749770269095496586449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130775332720717587990897197 49040749770269095496586449)
      ·
        refine ⟨36780562327701821622439837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49040749770269095496586449 36780562327701821622439837)
        ·
          refine ⟨13792710872888183108414939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36780562327701821622439837 13792710872888183108414939)
          ·
            refine ⟨20689066309332274662622409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13792710872888183108414939 20689066309332274662622409)
            ·
              refine ⟨15516799731999205996966807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20689066309332274662622409 15516799731999205996966807)
              ·
                refine ⟨23275199597998808995450211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15516799731999205996966807 23275199597998808995450211)
                ·
                  refine ⟨34912799396998213493175317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23275199597998808995450211 34912799396998213493175317)
                  ·
                    refine ⟨1636537471734291257492593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34912799396998213493175317 1636537471734291257492593)
                    ·
                      refine ⟨1227403103800718443119445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1636537471734291257492593 1227403103800718443119445)
                      ·
                        rfl

theorem cell23_2390359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_2390359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390359 prefixEnd_2390359 := by exact prefixLift 2390359
  have htrace : WordTrace (prefixWord ++ tailWord_2390359) baseStart_2390359 baseEnd_2390359 := by
    simpa [prefixWord, tailWord_2390359, baseEnd_2390359] using wordTrace_append hprefix tailTrace_2390359
  have hstable : (prefixWord ++ tailWord_2390359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390359).length < 2 ^ (prefixWord ++ tailWord_2390359).sum := by decide
  have hdescent : baseEnd_2390359 < baseStart_2390359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390376 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_2390376 : Nat := 118140960795 + 2390376 * 2 ^ 59
def prefixEnd_2390376 : Nat := 4983230072969 + 3 ^ 40 * 2390376 * 2
def baseEnd_2390376 : Nat := 1227411832971844876606867

theorem tailTrace_2390376 : CollatzResearch.WordTrace tailWord_2390376 prefixEnd_2390376 1227411832971844876606867 := by
  unfold tailWord_2390376
  simp only [CollatzResearch.WordTrace]
  refine ⟨43592087594041735281983491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58122783458722313709311321 43592087594041735281983491)
  ·
    refine ⟨65388131391062602922975237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43592087594041735281983491 65388131391062602922975237)
    ·
      refine ⟨12260274635824238048057857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65388131391062602922975237 12260274635824238048057857)
      ·
        refine ⟨9195205976868178536043393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12260274635824238048057857 9195205976868178536043393)
        ·
          refine ⟨6896404482651133902032545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9195205976868178536043393 6896404482651133902032545)
          ·
            refine ⟨5172303361988350426524409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6896404482651133902032545 5172303361988350426524409)
            ·
              refine ⟨3879227521491262819893307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5172303361988350426524409 3879227521491262819893307)
              ·
                refine ⟨5818841282236894229839961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3879227521491262819893307 5818841282236894229839961)
                ·
                  refine ⟨4364130961677670672379971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5818841282236894229839961 4364130961677670672379971)
                  ·
                    refine ⟨6546196442516506008569957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4364130961677670672379971 6546196442516506008569957)
                    ·
                      refine ⟨1227411832971844876606867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6546196442516506008569957 1227411832971844876606867)
                      ·
                        rfl

theorem cell23_2390376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_2390376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390376 prefixEnd_2390376 := by exact prefixLift 2390376
  have htrace : WordTrace (prefixWord ++ tailWord_2390376) baseStart_2390376 baseEnd_2390376 := by
    simpa [prefixWord, tailWord_2390376, baseEnd_2390376] using wordTrace_append hprefix tailTrace_2390376
  have hstable : (prefixWord ++ tailWord_2390376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390376).length < 2 ^ (prefixWord ++ tailWord_2390376).sum := by decide
  have hdescent : baseEnd_2390376 < baseStart_2390376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390403 : List Nat := [1, 1, 1, 3, 6, 1, 1, 4, 1, 4]
def baseStart_2390403 : Nat := 118140960795 + 2390403 * 2 ^ 59
def prefixEnd_2390403 : Nat := 4983230072969 + 3 ^ 40 * 2390403 * 2
def baseEnd_2390403 : Nat := 409141898983172090323081

theorem tailTrace_2390403 : CollatzResearch.WordTrace tailWord_2390403 prefixEnd_2390403 409141898983172090323081 := by
  unfold tailWord_2390403
  simp only [CollatzResearch.WordTrace]
  refine ⟨87185159958985654175199863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58123439972657102783466575 87185159958985654175199863)
  ·
    refine ⟨130777739938478481262799795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87185159958985654175199863 130777739938478481262799795)
    ·
      refine ⟨196166609907717721894199693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130777739938478481262799795 196166609907717721894199693)
      ·
        refine ⟨73562478715394145710324885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196166609907717721894199693 73562478715394145710324885)
        ·
          refine ⟨3448241189784100580171479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73562478715394145710324885 3448241189784100580171479)
          ·
            refine ⟨5172361784676150870257219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3448241189784100580171479 5172361784676150870257219)
            ·
              refine ⟨7758542677014226305385829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5172361784676150870257219 7758542677014226305385829)
              ·
                refine ⟨1454726751940167432259843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7758542677014226305385829 1454726751940167432259843)
                ·
                  refine ⟨2182090127910251148389765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1454726751940167432259843 2182090127910251148389765)
                  ·
                    refine ⟨409141898983172090323081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2182090127910251148389765 409141898983172090323081)
                    ·
                      rfl

theorem cell23_2390403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 1, 4].length) (baseStart_2390403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390403 prefixEnd_2390403 := by exact prefixLift 2390403
  have htrace : WordTrace (prefixWord ++ tailWord_2390403) baseStart_2390403 baseEnd_2390403 := by
    simpa [prefixWord, tailWord_2390403, baseEnd_2390403] using wordTrace_append hprefix tailTrace_2390403
  have hstable : (prefixWord ++ tailWord_2390403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390403).length < 2 ^ (prefixWord ++ tailWord_2390403).sum := by decide
  have hdescent : baseEnd_2390403 < baseStart_2390403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390426 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3]
def baseStart_2390426 : Nat := 118140960795 + 2390426 * 2 ^ 59
def prefixEnd_2390426 : Nat := 4983230072969 + 3 ^ 40 * 2390426 * 2
def baseEnd_2390426 : Nat := 1227437507004569680981637

theorem tailTrace_2390426 : CollatzResearch.WordTrace tailWord_2390426 prefixEnd_2390426 1227437507004569680981637 := by
  unfold tailWord_2390426
  simp only [CollatzResearch.WordTrace]
  refine ⟨21796499709475582275821783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58123999225268219402191421 21796499709475582275821783)
  ·
    refine ⟨32694749564213373413732675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21796499709475582275821783 32694749564213373413732675)
    ·
      refine ⟨49042124346320060120599013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32694749564213373413732675 49042124346320060120599013)
      ·
        refine ⟨9195398314935011272612315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49042124346320060120599013 9195398314935011272612315)
        ·
          refine ⟨13793097472402516908918473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9195398314935011272612315 13793097472402516908918473)
          ·
            refine ⟨10344823104301887681688855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13793097472402516908918473 10344823104301887681688855)
            ·
              refine ⟨15517234656452831522533283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10344823104301887681688855 15517234656452831522533283)
              ·
                refine ⟨23275851984679247283799925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15517234656452831522533283 23275851984679247283799925)
                ·
                  refine ⟨2182111123563679432856243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23275851984679247283799925 2182111123563679432856243)
                  ·
                    refine ⟨3273166685345519149284365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2182111123563679432856243 3273166685345519149284365)
                    ·
                      refine ⟨1227437507004569680981637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3273166685345519149284365 1227437507004569680981637)
                      ·
                        rfl

theorem cell23_2390426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_2390426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390426 prefixEnd_2390426 := by exact prefixLift 2390426
  have htrace : WordTrace (prefixWord ++ tailWord_2390426) baseStart_2390426 baseEnd_2390426 := by
    simpa [prefixWord, tailWord_2390426, baseEnd_2390426] using wordTrace_append hprefix tailTrace_2390426
  have hstable : (prefixWord ++ tailWord_2390426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390426).length < 2 ^ (prefixWord ++ tailWord_2390426).sum := by decide
  have hdescent : baseEnd_2390426 < baseStart_2390426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390430 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2390430 : Nat := 118140960795 + 2390430 * 2 ^ 59
def prefixEnd_2390430 : Nat := 4983230072969 + 3 ^ 40 * 2390430 * 2
def baseEnd_2390430 : Nat := 1227439560927187665331619

theorem tailTrace_2390430 : CollatzResearch.WordTrace tailWord_2390430 prefixEnd_2390430 1227439560927187665331619 := by
  unfold tailWord_2390430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10898268091235979723304093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58124096486591891857621829 10898268091235979723304093)
  ·
    refine ⟨4086850534213492396239035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10898268091235979723304093 4086850534213492396239035)
    ·
      refine ⟨6130275801320238594358553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4086850534213492396239035 6130275801320238594358553)
      ·
        refine ⟨4597706850990178945768915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6130275801320238594358553 4597706850990178945768915)
        ·
          refine ⟨6896560276485268418653373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4597706850990178945768915 6896560276485268418653373)
          ·
            refine ⟨2586210103681975656995015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6896560276485268418653373 2586210103681975656995015)
            ·
              refine ⟨3879315155522963485492523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586210103681975656995015 3879315155522963485492523)
              ·
                refine ⟨5818972733284445228238785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3879315155522963485492523 5818972733284445228238785)
                ·
                  refine ⟨4364229549963333921179089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5818972733284445228238785 4364229549963333921179089)
                  ·
                    refine ⟨3273172162472500440884317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4364229549963333921179089 3273172162472500440884317)
                    ·
                      refine ⟨1227439560927187665331619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3273172162472500440884317 1227439560927187665331619)
                      ·
                        rfl

theorem cell23_2390430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2390430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390430 prefixEnd_2390430 := by exact prefixLift 2390430
  have htrace : WordTrace (prefixWord ++ tailWord_2390430) baseStart_2390430 baseEnd_2390430 := by
    simpa [prefixWord, tailWord_2390430, baseEnd_2390430] using wordTrace_append hprefix tailTrace_2390430
  have hstable : (prefixWord ++ tailWord_2390430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390430).length < 2 ^ (prefixWord ++ tailWord_2390430).sum := by decide
  have hdescent : baseEnd_2390430 < baseStart_2390430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390460 : List Nat := [2, 2, 2, 4, 1, 1, 2, 4, 1, 1, 3]
def baseStart_2390460 : Nat := 118140960795 + 2390460 * 2 ^ 59
def prefixEnd_2390460 : Nat := 4983230072969 + 3 ^ 40 * 2390460 * 2
def baseEnd_2390460 : Nat := 1227454965346822547956481

theorem tailTrace_2390460 : CollatzResearch.WordTrace tailWord_2390460 prefixEnd_2390460 1227454965346822547956481 := by
  unfold tailWord_2390460
  simp only [CollatzResearch.WordTrace]
  refine ⟨43593619459889576455012417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58124825946519435273349889 43593619459889576455012417)
  ·
    refine ⟨32695214594917182341259313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43593619459889576455012417 32695214594917182341259313)
    ·
      refine ⟨24521410946187886755944485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32695214594917182341259313 24521410946187886755944485)
      ·
        refine ⟨4597764552410228766739591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24521410946187886755944485 4597764552410228766739591)
        ·
          refine ⟨6896646828615343150109387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4597764552410228766739591 6896646828615343150109387)
          ·
            refine ⟨10344970242923014725164081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6896646828615343150109387 10344970242923014725164081)
            ·
              refine ⟨7758727682192261043873061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10344970242923014725164081 7758727682192261043873061)
              ·
                refine ⟨1454761440411048945726199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7758727682192261043873061 1454761440411048945726199)
                ·
                  refine ⟨2182142160616573418589299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1454761440411048945726199 2182142160616573418589299)
                  ·
                    refine ⟨3273213240924860127883949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2182142160616573418589299 3273213240924860127883949)
                    ·
                      refine ⟨1227454965346822547956481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3273213240924860127883949 1227454965346822547956481)
                      ·
                        rfl

theorem cell23_2390460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_2390460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390460 prefixEnd_2390460 := by exact prefixLift 2390460
  have htrace : WordTrace (prefixWord ++ tailWord_2390460) baseStart_2390460 baseEnd_2390460 := by
    simpa [prefixWord, tailWord_2390460, baseEnd_2390460] using wordTrace_append hprefix tailTrace_2390460
  have hstable : (prefixWord ++ tailWord_2390460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390460).length < 2 ^ (prefixWord ++ tailWord_2390460).sum := by decide
  have hdescent : baseEnd_2390460 < baseStart_2390460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390486 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2390486 : Nat := 118140960795 + 2390486 * 2 ^ 59
def prefixEnd_2390486 : Nat := 4983230072969 + 3 ^ 40 * 2390486 * 2
def baseEnd_2390486 : Nat := 1227468315843839446231361

theorem tailTrace_2390486 : CollatzResearch.WordTrace tailWord_2390486 prefixEnd_2390486 1227468315843839446231361 := by
  unfold tailWord_2390486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5449261701105309959404457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58125458145123306233647541 5449261701105309959404457)
  ·
    refine ⟨4086946275828982469553343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5449261701105309959404457 4086946275828982469553343)
    ·
      refine ⟨6130419413743473704330015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4086946275828982469553343 6130419413743473704330015)
      ·
        refine ⟨9195629120615210556495023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6130419413743473704330015 9195629120615210556495023)
        ·
          refine ⟨13793443680922815834742535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9195629120615210556495023 13793443680922815834742535)
          ·
            refine ⟨20690165521384223752113803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13793443680922815834742535 20690165521384223752113803)
            ·
              refine ⟨31035248282076335628170705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20690165521384223752113803 31035248282076335628170705)
              ·
                refine ⟨23276436211557251721128029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31035248282076335628170705 23276436211557251721128029)
                ·
                  refine ⟨8728663579333969395423011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23276436211557251721128029 8728663579333969395423011)
                  ·
                    refine ⟨13092995369000954093134517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8728663579333969395423011 13092995369000954093134517)
                    ·
                      refine ⟨1227468315843839446231361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13092995369000954093134517 1227468315843839446231361)
                      ·
                        rfl

theorem cell23_2390486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2390486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390486 prefixEnd_2390486 := by exact prefixLift 2390486
  have htrace : WordTrace (prefixWord ++ tailWord_2390486) baseStart_2390486 baseEnd_2390486 := by
    simpa [prefixWord, tailWord_2390486, baseEnd_2390486] using wordTrace_append hprefix tailTrace_2390486
  have hstable : (prefixWord ++ tailWord_2390486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390486).length < 2 ^ (prefixWord ++ tailWord_2390486).sum := by decide
  have hdescent : baseEnd_2390486 < baseStart_2390486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390534 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2390534 : Nat := 118140960795 + 2390534 * 2 ^ 59
def prefixEnd_2390534 : Nat := 4983230072969 + 3 ^ 40 * 2390534 * 2
def baseEnd_2390534 : Nat := 1227492962915255258431141

theorem tailTrace_2390534 : CollatzResearch.WordTrace tailWord_2390534 prefixEnd_2390534 1227492962915255258431141 := by
  unfold tailWord_2390534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2724685560047220735881833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58126625281007375698812437 2724685560047220735881833)
  ·
    refine ⟨2043514170035415551911375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2724685560047220735881833 2043514170035415551911375)
    ·
      refine ⟨3065271255053123327867063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2043514170035415551911375 3065271255053123327867063)
      ·
        refine ⟨4597906882579684991800595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3065271255053123327867063 4597906882579684991800595)
        ·
          refine ⟨6896860323869527487700893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4597906882579684991800595 6896860323869527487700893)
          ·
            refine ⟨2586322621451072807887835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6896860323869527487700893 2586322621451072807887835)
            ·
              refine ⟨3879483932176609211831753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586322621451072807887835 3879483932176609211831753)
              ·
                refine ⟨2909612949132456908873815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3879483932176609211831753 2909612949132456908873815)
                ·
                  refine ⟨4364419423698685363310723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2909612949132456908873815 4364419423698685363310723)
                  ·
                    refine ⟨6546629135548028044966085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4364419423698685363310723 6546629135548028044966085)
                    ·
                      refine ⟨1227492962915255258431141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6546629135548028044966085 1227492962915255258431141)
                      ·
                        rfl

theorem cell23_2390534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2390534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390534 prefixEnd_2390534 := by exact prefixLift 2390534
  have htrace : WordTrace (prefixWord ++ tailWord_2390534) baseStart_2390534 baseEnd_2390534 := by
    simpa [prefixWord, tailWord_2390534, baseEnd_2390534] using wordTrace_append hprefix tailTrace_2390534
  have hstable : (prefixWord ++ tailWord_2390534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390534).length < 2 ^ (prefixWord ++ tailWord_2390534).sum := by decide
  have hdescent : baseEnd_2390534 < baseStart_2390534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390579 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 7]
def baseStart_2390579 : Nat := 118140960795 + 2390579 * 2 ^ 59
def prefixEnd_2390579 : Nat := 4983230072969 + 3 ^ 40 * 2390579 * 2
def baseEnd_2390579 : Nat := 136390674393856398040937

theorem tailTrace_2390579 : CollatzResearch.WordTrace tailWord_2390579 prefixEnd_2390579 136390674393856398040937 := by
  unfold tailWord_2390579
  simp only [CollatzResearch.WordTrace]
  refine ⟨87191579206348036233606791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58127719470898690822404527 87191579206348036233606791)
  ·
    refine ⟨130787368809522054350410187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87191579206348036233606791 130787368809522054350410187)
    ·
      refine ⟨196181053214283081525615281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130787368809522054350410187 196181053214283081525615281)
      ·
        refine ⟨147135789910712311144211461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196181053214283081525615281 147135789910712311144211461)
        ·
          refine ⟨27587960608258558339539649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147135789910712311144211461 27587960608258558339539649)
          ·
            refine ⟨20690970456193918754654737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27587960608258558339539649 20690970456193918754654737)
            ·
              refine ⟨15518227842145439065991053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20690970456193918754654737 15518227842145439065991053)
              ·
                refine ⟨5819335440804539649746645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15518227842145439065991053 5819335440804539649746645)
                ·
                  refine ⟨136390674393856398040937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5819335440804539649746645 136390674393856398040937)
                  ·
                    rfl

theorem cell23_2390579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 7].length) (baseStart_2390579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390579 prefixEnd_2390579 := by exact prefixLift 2390579
  have htrace : WordTrace (prefixWord ++ tailWord_2390579) baseStart_2390579 baseEnd_2390579 := by
    simpa [prefixWord, tailWord_2390579, baseEnd_2390579] using wordTrace_append hprefix tailTrace_2390579
  have hstable : (prefixWord ++ tailWord_2390579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390579).length < 2 ^ (prefixWord ++ tailWord_2390579).sum := by decide
  have hdescent : baseEnd_2390579 < baseStart_2390579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390586 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_2390586 : Nat := 118140960795 + 2390586 * 2 ^ 59
def prefixEnd_2390586 : Nat := 4983230072969 + 3 ^ 40 * 2390586 * 2
def baseEnd_2390586 : Nat := 1227519663909289054980901

theorem tailTrace_2390586 : CollatzResearch.WordTrace tailWord_2390586 prefixEnd_2390586 1227519663909289054980901 := by
  unfold tailWord_2390586
  simp only [CollatzResearch.WordTrace]
  refine ⟨21797958629330669107277903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58127889678215117619407741 21797958629330669107277903)
  ·
    refine ⟨32696937943996003660916855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21797958629330669107277903 32696937943996003660916855)
    ·
      refine ⟨49045406915994005491375283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32696937943996003660916855 49045406915994005491375283)
      ·
        refine ⟨73568110373991008237062925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49045406915994005491375283 73568110373991008237062925)
        ·
          refine ⟨27588041390246628088898597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73568110373991008237062925 27588041390246628088898597)
          ·
            refine ⟨5172757760671242766668487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27588041390246628088898597 5172757760671242766668487)
            ·
              refine ⟨7759136641006864150002731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5172757760671242766668487 7759136641006864150002731)
              ·
                refine ⟨11638704961510296225004097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7759136641006864150002731 11638704961510296225004097)
                ·
                  refine ⟨8729028721132722168753073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11638704961510296225004097 8729028721132722168753073)
                  ·
                    refine ⟨6546771540849541626564805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8729028721132722168753073 6546771540849541626564805)
                    ·
                      refine ⟨1227519663909289054980901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6546771540849541626564805 1227519663909289054980901)
                      ·
                        rfl

theorem cell23_2390586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_2390586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390586 prefixEnd_2390586 := by exact prefixLift 2390586
  have htrace : WordTrace (prefixWord ++ tailWord_2390586) baseStart_2390586 baseEnd_2390586 := by
    simpa [prefixWord, tailWord_2390586, baseEnd_2390586] using wordTrace_append hprefix tailTrace_2390586
  have hstable : (prefixWord ++ tailWord_2390586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390586).length < 2 ^ (prefixWord ++ tailWord_2390586).sum := by decide
  have hdescent : baseEnd_2390586 < baseStart_2390586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390703 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 6]
def baseStart_2390703 : Nat := 118140960795 + 2390703 * 2 ^ 59
def prefixEnd_2390703 : Nat := 4983230072969 + 3 ^ 40 * 2390703 * 2
def baseEnd_2390703 : Nat := 136397749016207233024207

theorem tailTrace_2390703 : CollatzResearch.WordTrace tailWord_2390703 prefixEnd_2390703 136397749016207233024207 := by
  unfold tailWord_2390703
  simp only [CollatzResearch.WordTrace]
  refine ⟨87196101857898805411120763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58130734571932536940747175 87196101857898805411120763)
  ·
    refine ⟨130794152786848208116681145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87196101857898805411120763 130794152786848208116681145)
    ·
      refine ⟨98095614590136156087510859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130794152786848208116681145 98095614590136156087510859)
      ·
        refine ⟨147143421885204234131266289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98095614590136156087510859 147143421885204234131266289)
        ·
          refine ⟨110357566413903175598449717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147143421885204234131266289 110357566413903175598449717)
          ·
            refine ⟨10346021851303422712354661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110357566413903175598449717 10346021851303422712354661)
            ·
              refine ⟨1939879097119391758566499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10346021851303422712354661 1939879097119391758566499)
              ·
                refine ⟨2909818645679087637849749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939879097119391758566499 2909818645679087637849749)
                ·
                  refine ⟨136397749016207233024207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2909818645679087637849749 136397749016207233024207)
                  ·
                    rfl

theorem cell23_2390703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 6].length) (baseStart_2390703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390703 prefixEnd_2390703 := by exact prefixLift 2390703
  have htrace : WordTrace (prefixWord ++ tailWord_2390703) baseStart_2390703 baseEnd_2390703 := by
    simpa [prefixWord, tailWord_2390703, baseEnd_2390703] using wordTrace_append hprefix tailTrace_2390703
  have hstable : (prefixWord ++ tailWord_2390703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390703).length < 2 ^ (prefixWord ++ tailWord_2390703).sum := by decide
  have hdescent : baseEnd_2390703 < baseStart_2390703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390713 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 5, 1, 3]
def baseStart_2390713 : Nat := 118140960795 + 2390713 * 2 ^ 59
def prefixEnd_2390713 : Nat := 4983230072969 + 3 ^ 40 * 2390713 * 2
def baseEnd_2390713 : Nat := 1227584875952410058092817

theorem tailTrace_2390713 : CollatzResearch.WordTrace tailWord_2390713 prefixEnd_2390713 1227584875952410058092817 := by
  unfold tailWord_2390713
  simp only [CollatzResearch.WordTrace]
  refine ⟨87196466587862577118984793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58130977725241718079323195 87196466587862577118984793)
  ·
    refine ⟨65397349940896932839238595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87196466587862577118984793 65397349940896932839238595)
    ·
      refine ⟨98096024911345399258857893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65397349940896932839238595 98096024911345399258857893)
      ·
        refine ⟨18393004670877262361035855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98096024911345399258857893 18393004670877262361035855)
        ·
          refine ⟨27589507006315893541553783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18393004670877262361035855 27589507006315893541553783)
          ·
            refine ⟨41384260509473840312330675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27589507006315893541553783 41384260509473840312330675)
            ·
              refine ⟨62076390764210760468496013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41384260509473840312330675 62076390764210760468496013)
              ·
                refine ⟨23278646536579035175686005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62076390764210760468496013 23278646536579035175686005)
                ·
                  refine ⟨2182373112804284547720563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23278646536579035175686005 2182373112804284547720563)
                  ·
                    refine ⟨3273559669206426821580845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2182373112804284547720563 3273559669206426821580845)
                    ·
                      refine ⟨1227584875952410058092817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3273559669206426821580845 1227584875952410058092817)
                      ·
                        rfl

theorem cell23_2390713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_2390713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390713 prefixEnd_2390713 := by exact prefixLift 2390713
  have htrace : WordTrace (prefixWord ++ tailWord_2390713) baseStart_2390713 baseEnd_2390713 := by
    simpa [prefixWord, tailWord_2390713, baseEnd_2390713] using wordTrace_append hprefix tailTrace_2390713
  have hstable : (prefixWord ++ tailWord_2390713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390713).length < 2 ^ (prefixWord ++ tailWord_2390713).sum := by decide
  have hdescent : baseEnd_2390713 < baseStart_2390713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390741 : List Nat := [1, 3, 2, 5, 1, 2, 2, 2, 1, 4]
def baseStart_2390741 : Nat := 118140960795 + 2390741 * 2 ^ 59
def prefixEnd_2390741 : Nat := 4983230072969 + 3 ^ 40 * 2390741 * 2
def baseEnd_2390741 : Nat := 409199751136911982847563

theorem tailTrace_2390741 : CollatzResearch.WordTrace tailWord_2390741 prefixEnd_2390741 409199751136911982847563 := by
  unfold tailWord_2390741
  simp only [CollatzResearch.WordTrace]
  refine ⟨87197487831761137901004077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58131658554507425267336051 87197487831761137901004077)
  ·
    refine ⟨32699057936910426712876529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87197487831761137901004077 32699057936910426712876529)
    ·
      refine ⟨24524293452682820034657397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32699057936910426712876529 24524293452682820034657397)
      ·
        refine ⟨2299152511189014378249131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24524293452682820034657397 2299152511189014378249131)
        ·
          refine ⟨3448728766783521567373697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299152511189014378249131 3448728766783521567373697)
          ·
            refine ⟨2586546575087641175530273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3448728766783521567373697 2586546575087641175530273)
            ·
              refine ⟨1939909931315730881647705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2586546575087641175530273 1939909931315730881647705)
              ·
                refine ⟨1454932448486798161235779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1939909931315730881647705 1454932448486798161235779)
                ·
                  refine ⟨2182398672730197241853669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1454932448486798161235779 2182398672730197241853669)
                  ·
                    refine ⟨409199751136911982847563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2182398672730197241853669 409199751136911982847563)
                    ·
                      rfl

theorem cell23_2390741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_2390741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390741 prefixEnd_2390741 := by exact prefixLift 2390741
  have htrace : WordTrace (prefixWord ++ tailWord_2390741) baseStart_2390741 baseEnd_2390741 := by
    simpa [prefixWord, tailWord_2390741, baseEnd_2390741] using wordTrace_append hprefix tailTrace_2390741
  have hstable : (prefixWord ++ tailWord_2390741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390741).length < 2 ^ (prefixWord ++ tailWord_2390741).sum := by decide
  have hdescent : baseEnd_2390741 < baseStart_2390741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390746 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_2390746 : Nat := 118140960795 + 2390746 * 2 ^ 59
def prefixEnd_2390746 : Nat := 4983230072969 + 3 ^ 40 * 2390746 * 2
def baseEnd_2390746 : Nat := 409200606938002809660055

theorem tailTrace_2390746 : CollatzResearch.WordTrace tailWord_2390746 prefixEnd_2390746 409200606938002809660055 := by
  unfold tailWord_2390746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21799417549185755938734023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58131780131162015836624061 21799417549185755938734023)
  ·
    refine ⟨32699126323778633908101035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21799417549185755938734023 32699126323778633908101035)
    ·
      refine ⟨49048689485667950862151553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32699126323778633908101035 49048689485667950862151553)
      ·
        refine ⟨36786517114250963146613665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49048689485667950862151553 36786517114250963146613665)
        ·
          refine ⟨27589887835688222359960249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36786517114250963146613665 27589887835688222359960249)
          ·
            refine ⟨20692415876766166769970187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27589887835688222359960249 20692415876766166769970187)
            ·
              refine ⟨31038623815149250154955281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20692415876766166769970187 31038623815149250154955281)
              ·
                refine ⟨23278967861361937616216461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31038623815149250154955281 23278967861361937616216461)
                ·
                  refine ⟨8729612948010726606081173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23278967861361937616216461 8729612948010726606081173)
                  ·
                    refine ⟨409200606938002809660055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8729612948010726606081173 409200606938002809660055)
                    ·
                      rfl

theorem cell23_2390746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_2390746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390746 prefixEnd_2390746 := by exact prefixLift 2390746
  have htrace : WordTrace (prefixWord ++ tailWord_2390746) baseStart_2390746 baseEnd_2390746 := by
    simpa [prefixWord, tailWord_2390746, baseEnd_2390746] using wordTrace_append hprefix tailTrace_2390746
  have hstable : (prefixWord ++ tailWord_2390746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390746).length < 2 ^ (prefixWord ++ tailWord_2390746).sum := by decide
  have hdescent : baseEnd_2390746 < baseStart_2390746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390753 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_2390753 : Nat := 118140960795 + 2390753 * 2 ^ 59
def prefixEnd_2390753 : Nat := 4983230072969 + 3 ^ 40 * 2390753 * 2
def baseEnd_2390753 : Nat := 1227605415178589901592633

theorem tailTrace_2390753 : CollatzResearch.WordTrace tailWord_2390753 prefixEnd_2390753 1227605415178589901592633 := by
  unfold tailWord_2390753
  simp only [CollatzResearch.WordTrace]
  refine ⟨87197925507717663950440913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58131950338478442633627275 87197925507717663950440913)
  ·
    refine ⟨65398444130788247962830685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87197925507717663950440913 65398444130788247962830685)
    ·
      refine ⟨24524416549045592986061507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65398444130788247962830685 24524416549045592986061507)
      ·
        refine ⟨36786624823568389479092261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24524416549045592986061507 36786624823568389479092261)
        ·
          refine ⟨6897492154419073027329799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36786624823568389479092261 6897492154419073027329799)
          ·
            refine ⟨10346238231628609540994699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6897492154419073027329799 10346238231628609540994699)
            ·
              refine ⟨15519357347442914311492049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10346238231628609540994699 15519357347442914311492049)
              ·
                refine ⟨11639518010582185733619037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15519357347442914311492049 11639518010582185733619037)
                ·
                  refine ⟨4364819253968319650107139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11639518010582185733619037 4364819253968319650107139)
                  ·
                    refine ⟨6547228880952479475160709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4364819253968319650107139 6547228880952479475160709)
                    ·
                      refine ⟨1227605415178589901592633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6547228880952479475160709 1227605415178589901592633)
                      ·
                        rfl

theorem cell23_2390753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_2390753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390753 prefixEnd_2390753 := by exact prefixLift 2390753
  have htrace : WordTrace (prefixWord ++ tailWord_2390753) baseStart_2390753 baseEnd_2390753 := by
    simpa [prefixWord, tailWord_2390753, baseEnd_2390753] using wordTrace_append hprefix tailTrace_2390753
  have hstable : (prefixWord ++ tailWord_2390753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390753).length < 2 ^ (prefixWord ++ tailWord_2390753).sum := by decide
  have hdescent : baseEnd_2390753 < baseStart_2390753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390796 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2390796 : Nat := 118140960795 + 2390796 * 2 ^ 59
def prefixEnd_2390796 : Nat := 4983230072969 + 3 ^ 40 * 2390796 * 2
def baseEnd_2390796 : Nat := 1227627494846733233354935

theorem tailTrace_2390796 : CollatzResearch.WordTrace tailWord_2390796 prefixEnd_2390796 1227627494846733233354935 := by
  unfold tailWord_2390796
  simp only [CollatzResearch.WordTrace]
  refine ⟨43599746923280941147128121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58132995897707921529504161 43599746923280941147128121)
  ·
    refine ⟨32699810192460705860346091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43599746923280941147128121 32699810192460705860346091)
    ·
      refine ⟨49049715288691058790519137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32699810192460705860346091 49049715288691058790519137)
      ·
        refine ⟨36787286466518294092889353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49049715288691058790519137 36787286466518294092889353)
        ·
          refine ⟨27590464849888720569667015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36787286466518294092889353 27590464849888720569667015)
          ·
            refine ⟨41385697274833080854500523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27590464849888720569667015 41385697274833080854500523)
            ·
              refine ⟨62078545912249621281750785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41385697274833080854500523 62078545912249621281750785)
              ·
                refine ⟨46558909434187215961313089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62078545912249621281750785 46558909434187215961313089)
                ·
                  refine ⟨34919182075640411970984817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46558909434187215961313089 34919182075640411970984817)
                  ·
                    refine ⟨26189386556730308978238613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34919182075640411970984817 26189386556730308978238613)
                    ·
                      refine ⟨1227627494846733233354935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26189386556730308978238613 1227627494846733233354935)
                      ·
                        rfl

theorem cell23_2390796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2390796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390796 prefixEnd_2390796 := by exact prefixLift 2390796
  have htrace : WordTrace (prefixWord ++ tailWord_2390796) baseStart_2390796 baseEnd_2390796 := by
    simpa [prefixWord, tailWord_2390796, baseEnd_2390796] using wordTrace_append hprefix tailTrace_2390796
  have hstable : (prefixWord ++ tailWord_2390796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390796).length < 2 ^ (prefixWord ++ tailWord_2390796).sum := by decide
  have hdescent : baseEnd_2390796 < baseStart_2390796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390847 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 1, 3, 2]
def baseStart_2390847 : Nat := 118140960795 + 2390847 * 2 ^ 59
def prefixEnd_2390847 : Nat := 4983230072969 + 3 ^ 40 * 2390847 * 2
def baseEnd_2390847 : Nat := 1227653682360112533817201

theorem tailTrace_2390847 : CollatzResearch.WordTrace tailWord_2390847 prefixEnd_2390847 1227653682360112533817201 := by
  unfold tailWord_2390847
  simp only [CollatzResearch.WordTrace]
  refine ⟨87201353969377118004362795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58134235979584745336241863 87201353969377118004362795)
  ·
    refine ⟨130802030954065677006544193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87201353969377118004362795 130802030954065677006544193)
    ·
      refine ⟨98101523215549257754908145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130802030954065677006544193 98101523215549257754908145)
      ·
        refine ⟨73576142411661943316181109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98101523215549257754908145 73576142411661943316181109)
        ·
          refine ⟨6897763351093307185891979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73576142411661943316181109 6897763351093307185891979)
          ·
            refine ⟨10346645026639960778837969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6897763351093307185891979 10346645026639960778837969)
            ·
              refine ⟨7759983769979970584128477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10346645026639960778837969 7759983769979970584128477)
              ·
                refine ⟨2909993913742488969048179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7759983769979970584128477 2909993913742488969048179)
                ·
                  refine ⟨4364990870613733453572269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2909993913742488969048179 4364990870613733453572269)
                  ·
                    refine ⟨1636871576480150045089601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4364990870613733453572269 1636871576480150045089601)
                    ·
                      refine ⟨1227653682360112533817201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1636871576480150045089601 1227653682360112533817201)
                      ·
                        rfl

theorem cell23_2390847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 3, 2].length) (baseStart_2390847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390847 prefixEnd_2390847 := by exact prefixLift 2390847
  have htrace : WordTrace (prefixWord ++ tailWord_2390847) baseStart_2390847 baseEnd_2390847 := by
    simpa [prefixWord, tailWord_2390847, baseEnd_2390847] using wordTrace_append hprefix tailTrace_2390847
  have hstable : (prefixWord ++ tailWord_2390847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390847).length < 2 ^ (prefixWord ++ tailWord_2390847).sum := by decide
  have hdescent : baseEnd_2390847 < baseStart_2390847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390894 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_2390894 : Nat := 118140960795 + 2390894 * 2 ^ 59
def prefixEnd_2390894 : Nat := 4983230072969 + 3 ^ 40 * 2390894 * 2
def baseEnd_2390894 : Nat := 1227677815950873849929485

theorem tailTrace_2390894 : CollatzResearch.WordTrace tailWord_2390894 prefixEnd_2390894 1227677815950873849929485 := by
  unfold tailWord_2390894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10900383525025855628915467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58135378800137896687549157 10900383525025855628915467)
  ·
    refine ⟨16350575287538783443373201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10900383525025855628915467 16350575287538783443373201)
    ·
      refine ⟨12262931465654087582529901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16350575287538783443373201 12262931465654087582529901)
      ·
        refine ⟨4598599299620282843448713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12262931465654087582529901 4598599299620282843448713)
        ·
          refine ⟨3448949474715212132586535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4598599299620282843448713 3448949474715212132586535)
          ·
            refine ⟨5173424212072818198879803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3448949474715212132586535 5173424212072818198879803)
            ·
              refine ⟨7760136318109227298319705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173424212072818198879803 7760136318109227298319705)
              ·
                refine ⟨5820102238581920473739779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7760136318109227298319705 5820102238581920473739779)
                ·
                  refine ⟨8730153357872880710609669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5820102238581920473739779 8730153357872880710609669)
                  ·
                    refine ⟨1636903754601165133239313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8730153357872880710609669 1636903754601165133239313)
                    ·
                      refine ⟨1227677815950873849929485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1636903754601165133239313 1227677815950873849929485)
                      ·
                        rfl

theorem cell23_2390894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_2390894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390894 prefixEnd_2390894 := by exact prefixLift 2390894
  have htrace : WordTrace (prefixWord ++ tailWord_2390894) baseStart_2390894 baseEnd_2390894 := by
    simpa [prefixWord, tailWord_2390894, baseEnd_2390894] using wordTrace_append hprefix tailTrace_2390894
  have hstable : (prefixWord ++ tailWord_2390894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390894).length < 2 ^ (prefixWord ++ tailWord_2390894).sum := by decide
  have hdescent : baseEnd_2390894 < baseStart_2390894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390917 : List Nat := [1, 3, 1, 1, 3, 3, 4, 2, 5]
def baseStart_2390917 : Nat := 118140960795 + 2390917 * 2 ^ 59
def prefixEnd_2390917 : Nat := 4983230072969 + 3 ^ 40 * 2390917 * 2
def baseEnd_2390917 : Nat := 136409958445103028882431

theorem tailTrace_2390917 : CollatzResearch.WordTrace tailWord_2390917 prefixEnd_2390917 136409958445103028882431 := by
  unfold tailWord_2390917
  simp only [CollatzResearch.WordTrace]
  refine ⟨87203907079123519959411005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58135938052749013306274003 87203907079123519959411005)
  ·
    refine ⟨32701465154671319984779127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87203907079123519959411005 32701465154671319984779127)
    ·
      refine ⟨49052197732006979977168691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32701465154671319984779127 49052197732006979977168691)
      ·
        refine ⟨73578296598010469965753037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49052197732006979977168691 73578296598010469965753037)
        ·
          refine ⟨27591861224253926237157389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73578296598010469965753037 27591861224253926237157389)
          ·
            refine ⟨10346947959095222338934021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27591861224253926237157389 10346947959095222338934021)
            ·
              refine ⟨1940052742330354188550129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10346947959095222338934021 1940052742330354188550129)
              ·
                refine ⟨1455039556747765641412597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1940052742330354188550129 1455039556747765641412597)
                ·
                  refine ⟨136409958445103028882431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1455039556747765641412597 136409958445103028882431)
                  ·
                    rfl

theorem cell23_2390917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_2390917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390917 prefixEnd_2390917 := by exact prefixLift 2390917
  have htrace : WordTrace (prefixWord ++ tailWord_2390917) baseStart_2390917 baseEnd_2390917 := by
    simpa [prefixWord, tailWord_2390917, baseEnd_2390917] using wordTrace_append hprefix tailTrace_2390917
  have hstable : (prefixWord ++ tailWord_2390917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390917).length < 2 ^ (prefixWord ++ tailWord_2390917).sum := by decide
  have hdescent : baseEnd_2390917 < baseStart_2390917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390923 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 5]
def baseStart_2390923 : Nat := 118140960795 + 2390923 * 2 ^ 59
def prefixEnd_2390923 : Nat := 4983230072969 + 3 ^ 40 * 2390923 * 2
def baseEnd_2390923 : Nat := 1227692706889854236466851

theorem tailTrace_2390923 : CollatzResearch.WordTrace tailWord_2390923 prefixEnd_2390923 1227692706889854236466851 := by
  unfold tailWord_2390923
  simp only [CollatzResearch.WordTrace]
  refine ⟨87204125917101782984129423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58136083944734521989419615 87204125917101782984129423)
  ·
    refine ⟨130806188875652674476194135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87204125917101782984129423 130806188875652674476194135)
    ·
      refine ⟨196209283313479011714291203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130806188875652674476194135 196209283313479011714291203)
      ·
        refine ⟨294313924970218517571436805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196209283313479011714291203 294313924970218517571436805)
        ·
          refine ⟨55183860931915972044644401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 294313924970218517571436805 55183860931915972044644401)
          ·
            refine ⟨41387895698936979033483301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55183860931915972044644401 41387895698936979033483301)
            ·
              refine ⟨7760230443550683568778119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41387895698936979033483301 7760230443550683568778119)
              ·
                refine ⟨11640345665326025353167179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7760230443550683568778119 11640345665326025353167179)
                ·
                  refine ⟨17460518497989038029750769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11640345665326025353167179 17460518497989038029750769)
                  ·
                    refine ⟨13095388873491778522313077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17460518497989038029750769 13095388873491778522313077)
                    ·
                      refine ⟨1227692706889854236466851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13095388873491778522313077 1227692706889854236466851)
                      ·
                        rfl

theorem cell23_2390923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 5].length) (baseStart_2390923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390923 prefixEnd_2390923 := by exact prefixLift 2390923
  have htrace : WordTrace (prefixWord ++ tailWord_2390923) baseStart_2390923 baseEnd_2390923 := by
    simpa [prefixWord, tailWord_2390923, baseEnd_2390923] using wordTrace_append hprefix tailTrace_2390923
  have hstable : (prefixWord ++ tailWord_2390923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390923).length < 2 ^ (prefixWord ++ tailWord_2390923).sum := by decide
  have hdescent : baseEnd_2390923 < baseStart_2390923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390934 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2390934 : Nat := 118140960795 + 2390934 * 2 ^ 59
def prefixEnd_2390934 : Nat := 4983230072969 + 3 ^ 40 * 2390934 * 2
def baseEnd_2390934 : Nat := 136410928353005965936589

theorem tailTrace_2390934 : CollatzResearch.WordTrace tailWord_2390934 prefixEnd_2390934 136410928353005965936589 := by
  unfold tailWord_2390934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5450282945003870741423741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58136351413374621241853237 5450282945003870741423741)
  ·
    refine ⟨2043856104376451528033903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5450282945003870741423741 2043856104376451528033903)
    ·
      refine ⟨3065784156564677292050855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2043856104376451528033903 3065784156564677292050855)
      ·
        refine ⟨4598676234847015938076283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3065784156564677292050855 4598676234847015938076283)
        ·
          refine ⟨6898014352270523907114425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4598676234847015938076283 6898014352270523907114425)
          ·
            refine ⟨5173510764202892930335819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6898014352270523907114425 5173510764202892930335819)
            ·
              refine ⟨7760266146304339395503729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173510764202892930335819 7760266146304339395503729)
              ·
                refine ⟨5820199609728254546627797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7760266146304339395503729 5820199609728254546627797)
                ·
                  refine ⟨136410928353005965936589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5820199609728254546627797 136410928353005965936589)
                  ·
                    rfl

theorem cell23_2390934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2390934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390934 prefixEnd_2390934 := by exact prefixLift 2390934
  have htrace : WordTrace (prefixWord ++ tailWord_2390934) baseStart_2390934 baseEnd_2390934 := by
    simpa [prefixWord, tailWord_2390934, baseEnd_2390934] using wordTrace_append hprefix tailTrace_2390934
  have hstable : (prefixWord ++ tailWord_2390934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390934).length < 2 ^ (prefixWord ++ tailWord_2390934).sum := by decide
  have hdescent : baseEnd_2390934 < baseStart_2390934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390970 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3]
def baseStart_2390970 : Nat := 118140960795 + 2390970 * 2 ^ 59
def prefixEnd_2390970 : Nat := 4983230072969 + 3 ^ 40 * 2390970 * 2
def baseEnd_2390970 : Nat := 1227716840480615552579135

theorem tailTrace_2390970 : CollatzResearch.WordTrace tailWord_2390970 prefixEnd_2390970 1227716840480615552579135 := by
  unfold tailWord_2390970
  simp only [CollatzResearch.WordTrace]
  refine ⟨21801460036982877502772591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58137226765287673340726909 21801460036982877502772591)
  ·
    refine ⟨32702190055474316254158887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21801460036982877502772591 32702190055474316254158887)
    ·
      refine ⟨49053285083211474381238331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32702190055474316254158887 49053285083211474381238331)
      ·
        refine ⟨73579927624817211571857497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49053285083211474381238331 73579927624817211571857497)
        ·
          refine ⟨55184945718612908678893123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73579927624817211571857497 55184945718612908678893123)
          ·
            refine ⟨82777418577919363018339685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55184945718612908678893123 82777418577919363018339685)
            ·
              refine ⟨15520765983359880565938691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82777418577919363018339685 15520765983359880565938691)
              ·
                refine ⟨23281148975039820848908037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15520765983359880565938691 23281148975039820848908037)
                ·
                  refine ⟨4365215432819966409170257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23281148975039820848908037 4365215432819966409170257)
                  ·
                    refine ⟨3273911574614974806877693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4365215432819966409170257 3273911574614974806877693)
                    ·
                      refine ⟨1227716840480615552579135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3273911574614974806877693 1227716840480615552579135)
                      ·
                        rfl

theorem cell23_2390970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_2390970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390970 prefixEnd_2390970 := by exact prefixLift 2390970
  have htrace : WordTrace (prefixWord ++ tailWord_2390970) baseStart_2390970 baseEnd_2390970 := by
    simpa [prefixWord, tailWord_2390970, baseEnd_2390970] using wordTrace_append hprefix tailTrace_2390970
  have hstable : (prefixWord ++ tailWord_2390970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390970).length < 2 ^ (prefixWord ++ tailWord_2390970).sum := by decide
  have hdescent : baseEnd_2390970 < baseStart_2390970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390993 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_2390993 : Nat := 118140960795 + 2390993 * 2 ^ 59
def prefixEnd_2390993 : Nat := 4983230072969 + 3 ^ 40 * 2390993 * 2
def baseEnd_2390993 : Nat := 1227728650535668962591529

theorem tailTrace_2390993 : CollatzResearch.WordTrace tailWord_2390993 prefixEnd_2390993 1227728650535668962591529 := by
  unfold tailWord_2390993
  simp only [CollatzResearch.WordTrace]
  refine ⟨87206679026848184939177633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58137786017898789959451755 87206679026848184939177633)
  ·
    refine ⟨65405009270136138704383225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87206679026848184939177633 65405009270136138704383225)
    ·
      refine ⟨49053756952602104028287419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65405009270136138704383225 49053756952602104028287419)
      ·
        refine ⟨73580635428903156042431129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49053756952602104028287419 73580635428903156042431129)
        ·
          refine ⟨55185476571677367031823347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73580635428903156042431129 55185476571677367031823347)
          ·
            refine ⟨82778214857516050547735021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55185476571677367031823347 82778214857516050547735021)
            ·
              refine ⟨31041830571568518955400633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82778214857516050547735021 31041830571568518955400633)
              ·
                refine ⟨23281372928676389216550475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31041830571568518955400633 23281372928676389216550475)
                ·
                  refine ⟨34922059393014583824825713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23281372928676389216550475 34922059393014583824825713)
                  ·
                    refine ⟨26191544544760937868619285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34922059393014583824825713 26191544544760937868619285)
                    ·
                      refine ⟨1227728650535668962591529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26191544544760937868619285 1227728650535668962591529)
                      ·
                        rfl

theorem cell23_2390993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_2390993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2390993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2390993 prefixEnd_2390993 := by exact prefixLift 2390993
  have htrace : WordTrace (prefixWord ++ tailWord_2390993) baseStart_2390993 baseEnd_2390993 := by
    simpa [prefixWord, tailWord_2390993, baseEnd_2390993] using wordTrace_append hprefix tailTrace_2390993
  have hstable : (prefixWord ++ tailWord_2390993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390993).length < 2 ^ (prefixWord ++ tailWord_2390993).sum := by decide
  have hdescent : baseEnd_2390993 < baseStart_2390993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391034 : List Nat := [3, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3]
def baseStart_2391034 : Nat := 118140960795 + 2391034 * 2 ^ 59
def prefixEnd_2391034 : Nat := 4983230072969 + 3 ^ 40 * 2391034 * 2
def baseEnd_2391034 : Nat := 1227749703242503302178841

theorem tailTrace_2391034 : CollatzResearch.WordTrace tailWord_2391034 prefixEnd_2391034 1227749703242503302178841 := by
  unfold tailWord_2391034
  simp only [CollatzResearch.WordTrace]
  refine ⟨21802043604924912235355039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58138782946466432627613437 21802043604924912235355039)
  ·
    refine ⟨32703065407387368353032559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21802043604924912235355039 32703065407387368353032559)
    ·
      refine ⟨49054598111081052529548839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32703065407387368353032559 49054598111081052529548839)
      ·
        refine ⟨73581897166621578794323259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49054598111081052529548839 73581897166621578794323259)
        ·
          refine ⟨110372845749932368191484889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73581897166621578794323259 110372845749932368191484889)
          ·
            refine ⟨82779634312449276143613667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110372845749932368191484889 82779634312449276143613667)
            ·
              refine ⟨124169451468673914215420501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82779634312449276143613667 124169451468673914215420501)
              ·
                refine ⟨1455110759398522432211959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 124169451468673914215420501 1455110759398522432211959)
                ·
                  refine ⟨2182666139097783648317939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455110759398522432211959 2182666139097783648317939)
                  ·
                    refine ⟨3273999208646675472476909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2182666139097783648317939 3273999208646675472476909)
                    ·
                      refine ⟨1227749703242503302178841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3273999208646675472476909 1227749703242503302178841)
                      ·
                        rfl

theorem cell23_2391034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3].length) (baseStart_2391034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391034 prefixEnd_2391034 := by exact prefixLift 2391034
  have htrace : WordTrace (prefixWord ++ tailWord_2391034) baseStart_2391034 baseEnd_2391034 := by
    simpa [prefixWord, tailWord_2391034, baseEnd_2391034] using wordTrace_append hprefix tailTrace_2391034
  have hstable : (prefixWord ++ tailWord_2391034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391034).length < 2 ^ (prefixWord ++ tailWord_2391034).sum := by decide
  have hdescent : baseEnd_2391034 < baseStart_2391034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391054 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_2391054 : Nat := 118140960795 + 2391054 * 2 ^ 59
def prefixEnd_2391054 : Nat := 4983230072969 + 3 ^ 40 * 2391054 * 2
def baseEnd_2391054 : Nat := 409253324285197741309583

theorem tailTrace_2391054 : CollatzResearch.WordTrace tailWord_2391054 prefixEnd_2391054 409253324285197741309583 := by
  unfold tailWord_2391054
  simp only [CollatzResearch.WordTrace]
  refine ⟨10901112984953399044643527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58139269253084794904765477 10901112984953399044643527)
  ·
    refine ⟨16351669477430098566965291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10901112984953399044643527 16351669477430098566965291)
    ·
      refine ⟨24527504216145147850447937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16351669477430098566965291 24527504216145147850447937)
      ·
        refine ⟨18395628162108860887835953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24527504216145147850447937 18395628162108860887835953)
        ·
          refine ⟨13796721121581645665876965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18395628162108860887835953 13796721121581645665876965)
          ·
            refine ⟨2586885210296558562351931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13796721121581645665876965 2586885210296558562351931)
            ·
              refine ⟨3880327815444837843527897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586885210296558562351931 3880327815444837843527897)
              ·
                refine ⟨2910245861583628382645923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3880327815444837843527897 2910245861583628382645923)
                ·
                  refine ⟨4365368792375442573968885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2910245861583628382645923 4365368792375442573968885)
                  ·
                    refine ⟨409253324285197741309583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4365368792375442573968885 409253324285197741309583)
                    ·
                      rfl

theorem cell23_2391054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_2391054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391054 prefixEnd_2391054 := by exact prefixLift 2391054
  have htrace : WordTrace (prefixWord ++ tailWord_2391054) baseStart_2391054 baseEnd_2391054 := by
    simpa [prefixWord, tailWord_2391054, baseEnd_2391054] using wordTrace_append hprefix tailTrace_2391054
  have hstable : (prefixWord ++ tailWord_2391054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391054).length < 2 ^ (prefixWord ++ tailWord_2391054).sum := by decide
  have hdescent : baseEnd_2391054 < baseStart_2391054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391094 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2391094 : Nat := 118140960795 + 2391094 * 2 ^ 59
def prefixEnd_2391094 : Nat := 4983230072969 + 3 ^ 40 * 2391094 * 2
def baseEnd_2391094 : Nat := 1227780512081773067428565

theorem tailTrace_2391094 : CollatzResearch.WordTrace tailWord_2391094 prefixEnd_2391094 1227780512081773067428565 := by
  unfold tailWord_2391094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5450647674967642449287771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58140241866321519459069557 5450647674967642449287771)
  ·
    refine ⟨8175971512451463673931657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5450647674967642449287771 8175971512451463673931657)
    ·
      refine ⟨6131978634338597755448743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8175971512451463673931657 6131978634338597755448743)
      ·
        refine ⟨9197967951507896633173115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6131978634338597755448743 9197967951507896633173115)
        ·
          refine ⟨13796951927261844949759673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9197967951507896633173115 13796951927261844949759673)
          ·
            refine ⟨10347713945446383712319755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13796951927261844949759673 10347713945446383712319755)
            ·
              refine ⟨15521570918169575568479633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10347713945446383712319755 15521570918169575568479633)
              ·
                refine ⟨11641178188627181676359725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15521570918169575568479633 11641178188627181676359725)
                ·
                  refine ⟨4365441820735193128634897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11641178188627181676359725 4365441820735193128634897)
                  ·
                    refine ⟨3274081365551394846476173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4365441820735193128634897 3274081365551394846476173)
                    ·
                      refine ⟨1227780512081773067428565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3274081365551394846476173 1227780512081773067428565)
                      ·
                        rfl

theorem cell23_2391094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2391094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391094 prefixEnd_2391094 := by exact prefixLift 2391094
  have htrace : WordTrace (prefixWord ++ tailWord_2391094) baseStart_2391094 baseEnd_2391094 := by
    simpa [prefixWord, tailWord_2391094, baseEnd_2391094] using wordTrace_append hprefix tailTrace_2391094
  have hstable : (prefixWord ++ tailWord_2391094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391094).length < 2 ^ (prefixWord ++ tailWord_2391094).sum := by decide
  have hdescent : baseEnd_2391094 < baseStart_2391094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391097 : List Nat := [1, 2, 1, 5, 2, 3, 1, 8]
def baseStart_2391097 : Nat := 118140960795 + 2391097 * 2 ^ 59
def prefixEnd_2391097 : Nat := 4983230072969 + 3 ^ 40 * 2391097 * 2
def baseEnd_2391097 : Nat := 45473409352730983544113

theorem tailTrace_2391097 : CollatzResearch.WordTrace tailWord_2391097 prefixEnd_2391097 45473409352730983544113 := by
  unfold tailWord_2391097
  simp only [CollatzResearch.WordTrace]
  refine ⟨87210472218471410700963545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58140314812314273800642363 87210472218471410700963545)
  ·
    refine ⟨65407854163853558025722659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87210472218471410700963545 65407854163853558025722659)
    ·
      refine ⟨98111781245780337038583989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65407854163853558025722659 98111781245780337038583989)
      ·
        refine ⟨9197979491791906597367249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98111781245780337038583989 9197979491791906597367249)
        ·
          refine ⟨6898484618843929948025437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9197979491791906597367249 6898484618843929948025437)
          ·
            refine ⟨2586931732066473730509539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6898484618843929948025437 2586931732066473730509539)
            ·
              refine ⟨3880397598099710595764309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586931732066473730509539 3880397598099710595764309)
              ·
                refine ⟨45473409352730983544113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3880397598099710595764309 45473409352730983544113)
                ·
                  rfl

theorem cell23_2391097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 8].length) (baseStart_2391097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391097 prefixEnd_2391097 := by exact prefixLift 2391097
  have htrace : WordTrace (prefixWord ++ tailWord_2391097) baseStart_2391097 baseEnd_2391097 := by
    simpa [prefixWord, tailWord_2391097, baseEnd_2391097] using wordTrace_append hprefix tailTrace_2391097
  have hstable : (prefixWord ++ tailWord_2391097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391097).length < 2 ^ (prefixWord ++ tailWord_2391097).sum := by decide
  have hdescent : baseEnd_2391097 < baseStart_2391097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391107 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 3]
def baseStart_2391107 : Nat := 118140960795 + 2391107 * 2 ^ 59
def prefixEnd_2391107 : Nat := 4983230072969 + 3 ^ 40 * 2391107 * 2
def baseEnd_2391107 : Nat := 1227787187330281516566005

theorem tailTrace_2391107 : CollatzResearch.WordTrace tailWord_2391107 prefixEnd_2391107 1227787187330281516566005 := by
  unfold tailWord_2391107
  simp only [CollatzResearch.WordTrace]
  refine ⟨87210836948435182408827575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58140557965623454939218383 87210836948435182408827575)
  ·
    refine ⟨130816255422652773613241363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87210836948435182408827575 130816255422652773613241363)
    ·
      refine ⟨196224383133979160419862045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130816255422652773613241363 196224383133979160419862045)
      ·
        refine ⟨73584143675242185157448267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196224383133979160419862045 73584143675242185157448267)
        ·
          refine ⟨110376215512863277736172401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73584143675242185157448267 110376215512863277736172401)
          ·
            refine ⟨82782161634647458302129301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110376215512863277736172401 82782161634647458302129301)
            ·
              refine ⟨3880413826624099607912311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82782161634647458302129301 3880413826624099607912311)
              ·
                refine ⟨5820620739936149411868467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3880413826624099607912311 5820620739936149411868467)
                ·
                  refine ⟨8730931109904224117802701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5820620739936149411868467 8730931109904224117802701)
                  ·
                    refine ⟨3274099166214084044176013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8730931109904224117802701 3274099166214084044176013)
                    ·
                      refine ⟨1227787187330281516566005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3274099166214084044176013 1227787187330281516566005)
                      ·
                        rfl

theorem cell23_2391107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_2391107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391107 prefixEnd_2391107 := by exact prefixLift 2391107
  have htrace : WordTrace (prefixWord ++ tailWord_2391107) baseStart_2391107 baseEnd_2391107 := by
    simpa [prefixWord, tailWord_2391107, baseEnd_2391107] using wordTrace_append hprefix tailTrace_2391107
  have hstable : (prefixWord ++ tailWord_2391107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391107).length < 2 ^ (prefixWord ++ tailWord_2391107).sum := by decide
  have hdescent : baseEnd_2391107 < baseStart_2391107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391130 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_2391130 : Nat := 118140960795 + 2391130 * 2 ^ 59
def prefixEnd_2391130 : Nat := 4983230072969 + 3 ^ 40 * 2391130 * 2
def baseEnd_2391130 : Nat := 1227798997385334926578399

theorem tailTrace_2391130 : CollatzResearch.WordTrace tailWord_2391130 prefixEnd_2391130 1227798997385334926578399 := by
  unfold tailWord_2391130
  simp only [CollatzResearch.WordTrace]
  refine ⟨21802918956837964334228711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58141117218234571557943229 21802918956837964334228711)
  ·
    refine ⟨32704378435256946501343067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21802918956837964334228711 32704378435256946501343067)
    ·
      refine ⟨49056567652885419752014601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32704378435256946501343067 49056567652885419752014601)
      ·
        refine ⟨36792425739664064814010951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49056567652885419752014601 36792425739664064814010951)
        ·
          refine ⟨55188638609496097221016427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36792425739664064814010951 55188638609496097221016427)
          ·
            refine ⟨82782957914244145831524641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55188638609496097221016427 82782957914244145831524641)
            ·
              refine ⟨62087218435683109373643481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82782957914244145831524641 62087218435683109373643481)
              ·
                refine ⟨46565413826762332030232611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62087218435683109373643481 46565413826762332030232611)
                ·
                  refine ⟨69848120740143498045348917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46565413826762332030232611 69848120740143498045348917)
                  ·
                    refine ⟨6548261319388452941751461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69848120740143498045348917 6548261319388452941751461)
                    ·
                      refine ⟨1227798997385334926578399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6548261319388452941751461 1227798997385334926578399)
                      ·
                        rfl

theorem cell23_2391130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_2391130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391130 prefixEnd_2391130 := by exact prefixLift 2391130
  have htrace : WordTrace (prefixWord ++ tailWord_2391130) baseStart_2391130 baseEnd_2391130 := by
    simpa [prefixWord, tailWord_2391130, baseEnd_2391130] using wordTrace_append hprefix tailTrace_2391130
  have hstable : (prefixWord ++ tailWord_2391130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391130).length < 2 ^ (prefixWord ++ tailWord_2391130).sum := by decide
  have hdescent : baseEnd_2391130 < baseStart_2391130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391158 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_2391158 : Nat := 118140960795 + 2391158 * 2 ^ 59
def prefixEnd_2391158 : Nat := 4983230072969 + 3 ^ 40 * 2391158 * 2
def baseEnd_2391158 : Nat := 1227813374843660817028271

theorem tailTrace_2391158 : CollatzResearch.WordTrace tailWord_2391158 prefixEnd_2391158 1227813374843660817028271 := by
  unfold tailWord_2391158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5450793566953151132433383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58141798047500278745956085 5450793566953151132433383)
  ·
    refine ⟨8176190350429726698650075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5450793566953151132433383 8176190350429726698650075)
    ·
      refine ⟨12264285525644590047975113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8176190350429726698650075 12264285525644590047975113)
      ·
        refine ⟨9198214144233442535981335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12264285525644590047975113 9198214144233442535981335)
        ·
          refine ⟨13797321216350163803972003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9198214144233442535981335 13797321216350163803972003)
          ·
            refine ⟨20695981824525245705958005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13797321216350163803972003 20695981824525245705958005)
            ·
              refine ⟨1940248296049241784933563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20695981824525245705958005 1940248296049241784933563)
              ·
                refine ⟨2910372444073862677400345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940248296049241784933563 2910372444073862677400345)
                ·
                  refine ⟨2182779333055397008050259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2910372444073862677400345 2182779333055397008050259)
                  ·
                    refine ⟨3274168999583095512075389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2182779333055397008050259 3274168999583095512075389)
                    ·
                      refine ⟨1227813374843660817028271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3274168999583095512075389 1227813374843660817028271)
                      ·
                        rfl

theorem cell23_2391158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_2391158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391158 prefixEnd_2391158 := by exact prefixLift 2391158
  have htrace : WordTrace (prefixWord ++ tailWord_2391158) baseStart_2391158 baseEnd_2391158 := by
    simpa [prefixWord, tailWord_2391158, baseEnd_2391158] using wordTrace_append hprefix tailTrace_2391158
  have hstable : (prefixWord ++ tailWord_2391158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391158).length < 2 ^ (prefixWord ++ tailWord_2391158).sum := by decide
  have hdescent : baseEnd_2391158 < baseStart_2391158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391198 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_2391198 : Nat := 118140960795 + 2391198 * 2 ^ 59
def prefixEnd_2391198 : Nat := 4983230072969 + 3 ^ 40 * 2391198 * 2
def baseEnd_2391198 : Nat := 1227833914069840660528087

theorem tailTrace_2391198 : CollatzResearch.WordTrace tailWord_2391198 prefixEnd_2391198 1227833914069840660528087 := by
  unfold tailWord_2391198
  simp only [CollatzResearch.WordTrace]
  refine ⟨10901769498888188118798781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58142770660737003300260165 10901769498888188118798781)
  ·
    refine ⟨4088163562083070544549543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10901769498888188118798781 4088163562083070544549543)
    ·
      refine ⟨6132245343124605816824315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4088163562083070544549543 6132245343124605816824315)
      ·
        refine ⟨9198368014686908725236473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6132245343124605816824315 9198368014686908725236473)
        ·
          refine ⟨6898776011015181543927355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9198368014686908725236473 6898776011015181543927355)
          ·
            refine ⟨10348164016522772315891033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6898776011015181543927355 10348164016522772315891033)
            ·
              refine ⟨7761123012392079236918275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10348164016522772315891033 7761123012392079236918275)
              ·
                refine ⟨11641684518588118855377413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7761123012392079236918275 11641684518588118855377413)
                ·
                  refine ⟨2182815847235272285383265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11641684518588118855377413 2182815847235272285383265)
                  ·
                    refine ⟨1637111885426454214037449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2182815847235272285383265 1637111885426454214037449)
                    ·
                      refine ⟨1227833914069840660528087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1637111885426454214037449 1227833914069840660528087)
                      ·
                        rfl

theorem cell23_2391198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_2391198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391198 prefixEnd_2391198 := by exact prefixLift 2391198
  have htrace : WordTrace (prefixWord ++ tailWord_2391198) baseStart_2391198 baseEnd_2391198 := by
    simpa [prefixWord, tailWord_2391198, baseEnd_2391198] using wordTrace_append hprefix tailTrace_2391198
  have hstable : (prefixWord ++ tailWord_2391198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391198).length < 2 ^ (prefixWord ++ tailWord_2391198).sum := by decide
  have hdescent : baseEnd_2391198 < baseStart_2391198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391204 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 7]
def baseStart_2391204 : Nat := 118140960795 + 2391204 * 2 ^ 59
def prefixEnd_2391204 : Nat := 4983230072969 + 3 ^ 40 * 2391204 * 2
def baseEnd_2391204 : Nat := 136426332772640848561451

theorem tailTrace_2391204 : CollatzResearch.WordTrace tailWord_2391204 prefixEnd_2391204 136426332772640848561451 := by
  unfold tailWord_2391204
  simp only [CollatzResearch.WordTrace]
  refine ⟨43607187414541883987554333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58142916552722511983405777 43607187414541883987554333)
  ·
    refine ⟨16352695280453206495332875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43607187414541883987554333 16352695280453206495332875)
    ·
      refine ⟨24529042920679809742999313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16352695280453206495332875 24529042920679809742999313)
      ·
        refine ⟨18396782190509857307249485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24529042920679809742999313 18396782190509857307249485)
        ·
          refine ⟨6898793321441196490218557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18396782190509857307249485 6898793321441196490218557)
          ·
            refine ⟨2587047495540448683831959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6898793321441196490218557 2587047495540448683831959)
            ·
              refine ⟨3880571243310673025747939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2587047495540448683831959 3880571243310673025747939)
              ·
                refine ⟨5820856864966009538621909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3880571243310673025747939 5820856864966009538621909)
                ·
                  refine ⟨136426332772640848561451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5820856864966009538621909 136426332772640848561451)
                  ·
                    rfl

theorem cell23_2391204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_2391204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391204 prefixEnd_2391204 := by exact prefixLift 2391204
  have htrace : WordTrace (prefixWord ++ tailWord_2391204) baseStart_2391204 baseEnd_2391204 := by
    simpa [prefixWord, tailWord_2391204, baseEnd_2391204] using wordTrace_append hprefix tailTrace_2391204
  have hstable : (prefixWord ++ tailWord_2391204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391204).length < 2 ^ (prefixWord ++ tailWord_2391204).sum := by decide
  have hdescent : baseEnd_2391204 < baseStart_2391204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391247 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 7, 4]
def baseStart_2391247 : Nat := 118140960795 + 2391247 * 2 ^ 59
def prefixEnd_2391247 : Nat := 4983230072969 + 3 ^ 40 * 2391247 * 2
def baseEnd_2391247 : Nat := 409286358207303656271787

theorem tailTrace_2391247 : CollatzResearch.WordTrace tailWord_2391247 prefixEnd_2391247 409286358207303656271787 := by
  unfold tailWord_2391247
  simp only [CollatzResearch.WordTrace]
  refine ⟨87215943167927986318923995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58143962111951990879282663 87215943167927986318923995)
  ·
    refine ⟨130823914751891979478385993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87215943167927986318923995 130823914751891979478385993)
    ·
      refine ⟨98117936063918984608789495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130823914751891979478385993 98117936063918984608789495)
      ·
        refine ⟨147176904095878476913184243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98117936063918984608789495 147176904095878476913184243)
        ·
          refine ⟨220765356143817715369776365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147176904095878476913184243 220765356143817715369776365)
          ·
            refine ⟨82787008553931643263666137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220765356143817715369776365 82787008553931643263666137)
            ·
              refine ⟨62090256415448732447749603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82787008553931643263666137 62090256415448732447749603)
              ·
                refine ⟨93135384623173098671624405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62090256415448732447749603 93135384623173098671624405)
                ·
                  refine ⟨2182860577105619500116197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 93135384623173098671624405 2182860577105619500116197)
                  ·
                    refine ⟨409286358207303656271787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2182860577105619500116197 409286358207303656271787)
                    ·
                      rfl

theorem cell23_2391247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 4].length) (baseStart_2391247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391247 prefixEnd_2391247 := by exact prefixLift 2391247
  have htrace : WordTrace (prefixWord ++ tailWord_2391247) baseStart_2391247 baseEnd_2391247 := by
    simpa [prefixWord, tailWord_2391247, baseEnd_2391247] using wordTrace_append hprefix tailTrace_2391247
  have hstable : (prefixWord ++ tailWord_2391247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391247).length < 2 ^ (prefixWord ++ tailWord_2391247).sum := by decide
  have hdescent : baseEnd_2391247 < baseStart_2391247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391257 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 3, 4, 3]
def baseStart_2391257 : Nat := 118140960795 + 2391257 * 2 ^ 59
def prefixEnd_2391257 : Nat := 4983230072969 + 3 ^ 40 * 2391257 * 2
def baseEnd_2391257 : Nat := 1227864209428455929690315

theorem tailTrace_2391257 : CollatzResearch.WordTrace tailWord_2391257 prefixEnd_2391257 1227864209428455929690315 := by
  unfold tailWord_2391257
  simp only [CollatzResearch.WordTrace]
  refine ⟨87216307897891758026788025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58144205265261172017858683 87216307897891758026788025)
  ·
    refine ⟨65412230923418818520091019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87216307897891758026788025 65412230923418818520091019)
    ·
      refine ⟨98118346385128227780136529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65412230923418818520091019 98118346385128227780136529)
      ·
        refine ⟨73588759788846170835102397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98118346385128227780136529 73588759788846170835102397)
        ·
          refine ⟨27595784920817314063163399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73588759788846170835102397 27595784920817314063163399)
          ·
            refine ⟨41393677381225971094745099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27595784920817314063163399 41393677381225971094745099)
            ·
              refine ⟨62090516071838956642117649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41393677381225971094745099 62090516071838956642117649)
              ·
                refine ⟨46567887053879217481588237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62090516071838956642117649 46567887053879217481588237)
                ·
                  refine ⟨17462957645204706555595589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46567887053879217481588237 17462957645204706555595589)
                  ·
                    refine ⟨3274304558475882479174173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17462957645204706555595589 3274304558475882479174173)
                    ·
                      refine ⟨1227864209428455929690315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3274304558475882479174173 1227864209428455929690315)
                      ·
                        rfl

theorem cell23_2391257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_2391257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391257 prefixEnd_2391257 := by exact prefixLift 2391257
  have htrace : WordTrace (prefixWord ++ tailWord_2391257) baseStart_2391257 baseEnd_2391257 := by
    simpa [prefixWord, tailWord_2391257, baseEnd_2391257] using wordTrace_append hprefix tailTrace_2391257
  have hstable : (prefixWord ++ tailWord_2391257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391257).length < 2 ^ (prefixWord ++ tailWord_2391257).sum := by decide
  have hdescent : baseEnd_2391257 < baseStart_2391257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391287 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 3]
def baseStart_2391287 : Nat := 118140960795 + 2391287 * 2 ^ 59
def prefixEnd_2391287 : Nat := 4983230072969 + 3 ^ 40 * 2391287 * 2
def baseEnd_2391287 : Nat := 1227879613848090812315177

theorem tailTrace_2391287 : CollatzResearch.WordTrace tailWord_2391287 prefixEnd_2391287 1227879613848090812315177 := by
  unfold tailWord_2391287
  simp only [CollatzResearch.WordTrace]
  refine ⟨87217402087783073150380115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58144934725188715433586743 87217402087783073150380115)
  ·
    refine ⟨130826103131674609725570173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87217402087783073150380115 130826103131674609725570173)
    ·
      refine ⟨49059788674377978647088815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130826103131674609725570173 49059788674377978647088815)
      ·
        refine ⟨73589683011566967970633223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49059788674377978647088815 73589683011566967970633223)
        ·
          refine ⟨110384524517350451955949835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73589683011566967970633223 110384524517350451955949835)
          ·
            refine ⟨165576786776025677933924753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110384524517350451955949835 165576786776025677933924753)
            ·
              refine ⟨124182590082019258450443565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165576786776025677933924753 124182590082019258450443565)
              ·
                refine ⟨46568471280757221918916337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124182590082019258450443565 46568471280757221918916337)
                ·
                  refine ⟨34926353460567916439187253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46568471280757221918916337 34926353460567916439187253)
                  ·
                    refine ⟨3274345636928242166173805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34926353460567916439187253 3274345636928242166173805)
                    ·
                      refine ⟨1227879613848090812315177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3274345636928242166173805 1227879613848090812315177)
                      ·
                        rfl

theorem cell23_2391287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_2391287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391287 prefixEnd_2391287 := by exact prefixLift 2391287
  have htrace : WordTrace (prefixWord ++ tailWord_2391287) baseStart_2391287 baseEnd_2391287 := by
    simpa [prefixWord, tailWord_2391287, baseEnd_2391287] using wordTrace_append hprefix tailTrace_2391287
  have hstable : (prefixWord ++ tailWord_2391287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391287).length < 2 ^ (prefixWord ++ tailWord_2391287).sum := by decide
  have hdescent : baseEnd_2391287 < baseStart_2391287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391338 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2391338 : Nat := 118140960795 + 2391338 * 2 ^ 59
def prefixEnd_2391338 : Nat := 4983230072969 + 3 ^ 40 * 2391338 * 2
def baseEnd_2391338 : Nat := 1227905801361470112777443

theorem tailTrace_2391338 : CollatzResearch.WordTrace tailWord_2391338 prefixEnd_2391338 1227905801361470112777443 := by
  unfold tailWord_2391338
  simp only [CollatzResearch.WordTrace]
  refine ⟨21804815552649577215121667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58146174807065539240324445 21804815552649577215121667)
  ·
    refine ⟨32707223328974365822682501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21804815552649577215121667 32707223328974365822682501)
    ·
      refine ⟨6132604374182693591752969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32707223328974365822682501 6132604374182693591752969)
      ·
        refine ⟨4599453280637020193814727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6132604374182693591752969 4599453280637020193814727)
        ·
          refine ⟨6899179920955530290722091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4599453280637020193814727 6899179920955530290722091)
          ·
            refine ⟨10348769881433295436083137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6899179920955530290722091 10348769881433295436083137)
            ·
              refine ⟨7761577411074971577062353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10348769881433295436083137 7761577411074971577062353)
              ·
                refine ⟨5821183058306228682796765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7761577411074971577062353 5821183058306228682796765)
                ·
                  refine ⟨2182943646864835756048787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5821183058306228682796765 2182943646864835756048787)
                  ·
                    refine ⟨3274415470297253634073181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2182943646864835756048787 3274415470297253634073181)
                    ·
                      refine ⟨1227905801361470112777443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3274415470297253634073181 1227905801361470112777443)
                      ·
                        rfl

theorem cell23_2391338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2391338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391338 prefixEnd_2391338 := by exact prefixLift 2391338
  have htrace : WordTrace (prefixWord ++ tailWord_2391338) baseStart_2391338 baseEnd_2391338 := by
    simpa [prefixWord, tailWord_2391338, baseEnd_2391338] using wordTrace_append hprefix tailTrace_2391338
  have hstable : (prefixWord ++ tailWord_2391338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391338).length < 2 ^ (prefixWord ++ tailWord_2391338).sum := by decide
  have hdescent : baseEnd_2391338 < baseStart_2391338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391344 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 2, 6, 2]
def baseStart_2391344 : Nat := 118140960795 + 2391344 * 2 ^ 59
def prefixEnd_2391344 : Nat := 4983230072969 + 3 ^ 40 * 2391344 * 2
def baseEnd_2391344 : Nat := 1227908882245397089302415

theorem tailTrace_2391344 : CollatzResearch.WordTrace tailWord_2391344 prefixEnd_2391344 1227908882245397089302415 := by
  unfold tailWord_2391344
  simp only [CollatzResearch.WordTrace]
  refine ⟨43609740524288285942602543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58146320699051047923470057 43609740524288285942602543)
  ·
    refine ⟨65414610786432428913903815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43609740524288285942602543 65414610786432428913903815)
    ·
      refine ⟨98121916179648643370855723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65414610786432428913903815 98121916179648643370855723)
      ·
        refine ⟨147182874269472965056283585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98121916179648643370855723 147182874269472965056283585)
        ·
          refine ⟨110387155702104723792212689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147182874269472965056283585 110387155702104723792212689)
          ·
            refine ⟨82790366776578542844159517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110387155702104723792212689 82790366776578542844159517)
            ·
              refine ⟨31046387541216953566559819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82790366776578542844159517 31046387541216953566559819)
              ·
                refine ⟨46569581311825430349839729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31046387541216953566559819 46569581311825430349839729)
                ·
                  refine ⟨34927185983869072762379797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46569581311825430349839729 34927185983869072762379797)
                  ·
                    refine ⟨1637211842993862785736553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34927185983869072762379797 1637211842993862785736553)
                    ·
                      refine ⟨1227908882245397089302415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1637211842993862785736553 1227908882245397089302415)
                      ·
                        rfl

theorem cell23_2391344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 6, 2].length) (baseStart_2391344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391344 prefixEnd_2391344 := by exact prefixLift 2391344
  have htrace : WordTrace (prefixWord ++ tailWord_2391344) baseStart_2391344 baseEnd_2391344 := by
    simpa [prefixWord, tailWord_2391344, baseEnd_2391344] using wordTrace_append hprefix tailTrace_2391344
  have hstable : (prefixWord ++ tailWord_2391344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391344).length < 2 ^ (prefixWord ++ tailWord_2391344).sum := by decide
  have hdescent : baseEnd_2391344 < baseStart_2391344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391348 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_2391348 : Nat := 118140960795 + 2391348 * 2 ^ 59
def prefixEnd_2391348 : Nat := 4983230072969 + 3 ^ 40 * 2391348 * 2
def baseEnd_2391348 : Nat := 1227910936168015073652397

theorem tailTrace_2391348 : CollatzResearch.WordTrace tailWord_2391348 prefixEnd_2391348 1227910936168015073652397 := by
  unfold tailWord_2391348
  simp only [CollatzResearch.WordTrace]
  refine ⟨43609813470281040284175349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58146417960374720378900465 43609813470281040284175349)
  ·
    refine ⟨4088420012838847526641439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43609813470281040284175349 4088420012838847526641439)
    ·
      refine ⟨6132630019258271289962159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4088420012838847526641439 6132630019258271289962159)
      ·
        refine ⟨9198945028887406934943239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6132630019258271289962159 9198945028887406934943239)
        ·
          refine ⟨13798417543331110402414859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9198945028887406934943239 13798417543331110402414859)
          ·
            refine ⟨20697626314996665603622289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13798417543331110402414859 20697626314996665603622289)
            ·
              refine ⟨15523219736247499202716717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20697626314996665603622289 15523219736247499202716717)
              ·
                refine ⟨5821207401092812201018769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15523219736247499202716717 5821207401092812201018769)
                ·
                  refine ⟨4365905550819609150764077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5821207401092812201018769 4365905550819609150764077)
                  ·
                    refine ⟨1637214581557353431536529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4365905550819609150764077 1637214581557353431536529)
                    ·
                      refine ⟨1227910936168015073652397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1637214581557353431536529 1227910936168015073652397)
                      ·
                        rfl

theorem cell23_2391348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_2391348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391348 prefixEnd_2391348 := by exact prefixLift 2391348
  have htrace : WordTrace (prefixWord ++ tailWord_2391348) baseStart_2391348 baseEnd_2391348 := by
    simpa [prefixWord, tailWord_2391348, baseEnd_2391348] using wordTrace_append hprefix tailTrace_2391348
  have hstable : (prefixWord ++ tailWord_2391348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391348).length < 2 ^ (prefixWord ++ tailWord_2391348).sum := by decide
  have hdescent : baseEnd_2391348 < baseStart_2391348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391354 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 6, 4]
def baseStart_2391354 : Nat := 118140960795 + 2391354 * 2 ^ 59
def prefixEnd_2391354 : Nat := 4983230072969 + 3 ^ 40 * 2391354 * 2
def baseEnd_2391354 : Nat := 409304672350647350059123

theorem tailTrace_2391354 : CollatzResearch.WordTrace tailWord_2391354 prefixEnd_2391354 409304672350647350059123 := by
  unfold tailWord_2391354
  simp only [CollatzResearch.WordTrace]
  refine ⟨21804961444635085898267279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58146563852360229062046077 21804961444635085898267279)
  ·
    refine ⟨32707442166952628847400919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21804961444635085898267279 32707442166952628847400919)
    ·
      refine ⟨49061163250428943271101379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32707442166952628847400919 49061163250428943271101379)
      ·
        refine ⟨73591744875643414906652069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49061163250428943271101379 73591744875643414906652069)
        ·
          refine ⟨13798452164183140294997263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73591744875643414906652069 13798452164183140294997263)
          ·
            refine ⟨20697678246274710442495895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13798452164183140294997263 20697678246274710442495895)
            ·
              refine ⟨31046517369412065663743843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20697678246274710442495895 31046517369412065663743843)
              ·
                refine ⟨46569776054118098495615765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31046517369412065663743843 46569776054118098495615765)
                ·
                  refine ⟨2182958252536785866981989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46569776054118098495615765 2182958252536785866981989)
                  ·
                    refine ⟨409304672350647350059123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2182958252536785866981989 409304672350647350059123)
                    ·
                      rfl

theorem cell23_2391354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_2391354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391354 prefixEnd_2391354 := by exact prefixLift 2391354
  have htrace : WordTrace (prefixWord ++ tailWord_2391354) baseStart_2391354 baseEnd_2391354 := by
    simpa [prefixWord, tailWord_2391354, baseEnd_2391354] using wordTrace_append hprefix tailTrace_2391354
  have hstable : (prefixWord ++ tailWord_2391354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391354).length < 2 ^ (prefixWord ++ tailWord_2391354).sum := by decide
  have hdescent : baseEnd_2391354 < baseStart_2391354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391367 : List Nat := [1, 1, 4, 1, 2, 3, 11]
def baseStart_2391367 : Nat := 118140960795 + 2391367 * 2 ^ 59
def prefixEnd_2391367 : Nat := 4983230072969 + 3 ^ 40 * 2391367 * 2
def baseEnd_2391367 : Nat := 15159514719758648139689

theorem tailTrace_2391367 : CollatzResearch.WordTrace tailWord_2391367 prefixEnd_2391367 15159514719758648139689 := by
  unfold tailWord_2391367
  simp only [CollatzResearch.WordTrace]
  refine ⟨87220319927493246813292355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58146879951662164542194903 87220319927493246813292355)
  ·
    refine ⟨130830479891239870219938533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87220319927493246813292355 130830479891239870219938533)
    ·
      refine ⟨24530714979607475666238475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130830479891239870219938533 24530714979607475666238475)
      ·
        refine ⟨36796072469411213499357713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24530714979607475666238475 36796072469411213499357713)
        ·
          refine ⟨27597054352058410124518285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36796072469411213499357713 27597054352058410124518285)
          ·
            refine ⟨10348895382021903796694357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27597054352058410124518285 10348895382021903796694357)
            ·
              refine ⟨15159514719758648139689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10348895382021903796694357 15159514719758648139689)
              ·
                rfl

theorem cell23_2391367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 11].length) (baseStart_2391367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391367 prefixEnd_2391367 := by exact prefixLift 2391367
  have htrace : WordTrace (prefixWord ++ tailWord_2391367) baseStart_2391367 baseEnd_2391367 := by
    simpa [prefixWord, tailWord_2391367, baseEnd_2391367] using wordTrace_append hprefix tailTrace_2391367
  have hstable : (prefixWord ++ tailWord_2391367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391367).length < 2 ^ (prefixWord ++ tailWord_2391367).sum := by decide
  have hdescent : baseEnd_2391367 < baseStart_2391367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391422 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2391422 : Nat := 118140960795 + 2391422 * 2 ^ 59
def prefixEnd_2391422 : Nat := 4983230072969 + 3 ^ 40 * 2391422 * 2
def baseEnd_2391422 : Nat := 409316311245482594709019

theorem tailTrace_2391422 : CollatzResearch.WordTrace tailWord_2391422 prefixEnd_2391422 409316311245482594709019 := by
  unfold tailWord_2391422
  simp only [CollatzResearch.WordTrace]
  refine ⟨10902790742786748900818065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58148217294862660804363013 10902790742786748900818065)
  ·
    refine ⟨8177093057090061675613549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10902790742786748900818065 8177093057090061675613549)
    ·
      refine ⟨3066409896408773128355081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8177093057090061675613549 3066409896408773128355081)
      ·
        refine ⟨2299807422306579846266311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3066409896408773128355081 2299807422306579846266311)
        ·
          refine ⟨3449711133459869769399467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299807422306579846266311 3449711133459869769399467)
          ·
            refine ⟨5174566700189804654099201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3449711133459869769399467 5174566700189804654099201)
            ·
              refine ⟨3880925025142353490574401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5174566700189804654099201 3880925025142353490574401)
              ·
                refine ⟨2910693768856765117930801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3880925025142353490574401 2910693768856765117930801)
                ·
                  refine ⟨2183020326642573838448101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2910693768856765117930801 2183020326642573838448101)
                  ·
                    refine ⟨409316311245482594709019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2183020326642573838448101 409316311245482594709019)
                    ·
                      rfl

theorem cell23_2391422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2391422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391422 prefixEnd_2391422 := by exact prefixLift 2391422
  have htrace : WordTrace (prefixWord ++ tailWord_2391422) baseStart_2391422 baseEnd_2391422 := by
    simpa [prefixWord, tailWord_2391422, baseEnd_2391422] using wordTrace_append hprefix tailTrace_2391422
  have hstable : (prefixWord ++ tailWord_2391422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391422).length < 2 ^ (prefixWord ++ tailWord_2391422).sum := by decide
  have hdescent : baseEnd_2391422 < baseStart_2391422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391428 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_2391428 : Nat := 118140960795 + 2391428 * 2 ^ 59
def prefixEnd_2391428 : Nat := 4983230072969 + 3 ^ 40 * 2391428 * 2
def baseEnd_2391428 : Nat := 1227952014620374760652029

theorem tailTrace_2391428 : CollatzResearch.WordTrace tailWord_2391428 prefixEnd_2391428 1227952014620374760652029 := by
  unfold tailWord_2391428
  simp only [CollatzResearch.WordTrace]
  refine ⟨43611272390136127115631469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58148363186848169487508625 43611272390136127115631469)
  ·
    refine ⟨16354227146301047668361801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43611272390136127115631469 16354227146301047668361801)
    ·
      refine ⟨12265670359725785751271351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16354227146301047668361801 12265670359725785751271351)
      ·
        refine ⟨18398505539588678626907027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12265670359725785751271351 18398505539588678626907027)
        ·
          refine ⟨27597758309383017940360541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18398505539588678626907027 27597758309383017940360541)
          ·
            refine ⟨10349159366018631727635203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27597758309383017940360541 10349159366018631727635203)
            ·
              refine ⟨15523739049027947591452805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10349159366018631727635203 15523739049027947591452805)
              ·
                refine ⟨2910701071692740173397401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15523739049027947591452805 2910701071692740173397401)
                ·
                  refine ⟨2183025803769555130048051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2910701071692740173397401 2183025803769555130048051)
                  ·
                    refine ⟨3274538705654332695072077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2183025803769555130048051 3274538705654332695072077)
                    ·
                      refine ⟨1227952014620374760652029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3274538705654332695072077 1227952014620374760652029)
                      ·
                        rfl

theorem cell23_2391428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_2391428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391428 prefixEnd_2391428 := by exact prefixLift 2391428
  have htrace : WordTrace (prefixWord ++ tailWord_2391428) baseStart_2391428 baseEnd_2391428 := by
    simpa [prefixWord, tailWord_2391428, baseEnd_2391428] using wordTrace_append hprefix tailTrace_2391428
  have hstable : (prefixWord ++ tailWord_2391428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391428).length < 2 ^ (prefixWord ++ tailWord_2391428).sum := by decide
  have hdescent : baseEnd_2391428 < baseStart_2391428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391491 : List Nat := [1, 1, 1, 3, 1, 1, 6, 4, 5]
def baseStart_2391491 : Nat := 118140960795 + 2391491 * 2 ^ 59
def prefixEnd_2391491 : Nat := 4983230072969 + 3 ^ 40 * 2391491 * 2
def baseEnd_2391491 : Nat := 136442707100178668240471

theorem tailTrace_2391491 : CollatzResearch.WordTrace tailWord_2391491 prefixEnd_2391491 136442707100178668240471 := by
  unfold tailWord_2391491
  simp only [CollatzResearch.WordTrace]
  refine ⟨87224842579044015990806327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58149895052696010660537551 87224842579044015990806327)
  ·
    refine ⟨130837263868566023986209491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87224842579044015990806327 130837263868566023986209491)
    ·
      refine ⟨196255895802849035979314237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130837263868566023986209491 196255895802849035979314237)
      ·
        refine ⟨73595960926068388492242839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196255895802849035979314237 73595960926068388492242839)
        ·
          refine ⟨110393941389102582738364259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73595960926068388492242839 110393941389102582738364259)
          ·
            refine ⟨165590912083653874107546389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110393941389102582738364259 165590912083653874107546389)
            ·
              refine ⟨7762074003921275348791237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 165590912083653874107546389 7762074003921275348791237)
              ·
                refine ⟨1455388875735239127898357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7762074003921275348791237 1455388875735239127898357)
                ·
                  refine ⟨136442707100178668240471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1455388875735239127898357 136442707100178668240471)
                  ·
                    rfl

theorem cell23_2391491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 5].length) (baseStart_2391491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391491 prefixEnd_2391491 := by exact prefixLift 2391491
  have htrace : WordTrace (prefixWord ++ tailWord_2391491) baseStart_2391491 baseEnd_2391491 := by
    simpa [prefixWord, tailWord_2391491, baseEnd_2391491] using wordTrace_append hprefix tailTrace_2391491
  have hstable : (prefixWord ++ tailWord_2391491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391491).length < 2 ^ (prefixWord ++ tailWord_2391491).sum := by decide
  have hdescent : baseEnd_2391491 < baseStart_2391491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391504 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 4, 5]
def baseStart_2391504 : Nat := 118140960795 + 2391504 * 2 ^ 59
def prefixEnd_2391504 : Nat := 4983230072969 + 3 ^ 40 * 2391504 * 2
def baseEnd_2391504 : Nat := 409330346383372154433893

theorem tailTrace_2391504 : CollatzResearch.WordTrace tailWord_2391504 prefixEnd_2391504 409330346383372154433893 := by
  unfold tailWord_2391504
  simp only [CollatzResearch.WordTrace]
  refine ⟨43612658363998459605514783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58150211151997946140686377 43612658363998459605514783)
  ·
    refine ⟨65418987545997689408272175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43612658363998459605514783 65418987545997689408272175)
    ·
      refine ⟨98128481318996534112408263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65418987545997689408272175 98128481318996534112408263)
      ·
        refine ⟨147192721978494801168612395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98128481318996534112408263 147192721978494801168612395)
        ·
          refine ⟨220789082967742201752918593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147192721978494801168612395 220789082967742201752918593)
          ·
            refine ⟨165591812225806651314688945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220789082967742201752918593 165591812225806651314688945)
            ·
              refine ⟨124193859169354988486016709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165591812225806651314688945 124193859169354988486016709)
              ·
                refine ⟨23286348594254060341128133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124193859169354988486016709 23286348594254060341128133)
                ·
                  refine ⟨4366190361422636313961525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23286348594254060341128133 4366190361422636313961525)
                  ·
                    refine ⟨409330346383372154433893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4366190361422636313961525 409330346383372154433893)
                    ·
                      rfl

theorem cell23_2391504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_2391504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391504 prefixEnd_2391504 := by exact prefixLift 2391504
  have htrace : WordTrace (prefixWord ++ tailWord_2391504) baseStart_2391504 baseEnd_2391504 := by
    simpa [prefixWord, tailWord_2391504, baseEnd_2391504] using wordTrace_append hprefix tailTrace_2391504
  have hstable : (prefixWord ++ tailWord_2391504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391504).length < 2 ^ (prefixWord ++ tailWord_2391504).sum := by decide
  have hdescent : baseEnd_2391504 < baseStart_2391504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391511 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 2, 5, 2]
def baseStart_2391511 : Nat := 118140960795 + 2391511 * 2 ^ 59
def prefixEnd_2391511 : Nat := 4983230072969 + 3 ^ 40 * 2391511 * 2
def baseEnd_2391511 : Nat := 1227994633514697935914147

theorem tailTrace_2391511 : CollatzResearch.WordTrace tailWord_2391511 prefixEnd_2391511 1227994633514697935914147 := by
  unfold tailWord_2391511
  simp only [CollatzResearch.WordTrace]
  refine ⟨87225572038971559406534387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58150381359314372937689591 87225572038971559406534387)
  ·
    refine ⟨130838358058457339109801581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87225572038971559406534387 130838358058457339109801581)
    ·
      refine ⟨49064384271921502166175593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130838358058457339109801581 49064384271921502166175593)
      ·
        refine ⟨36798288203941126624631695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49064384271921502166175593 36798288203941126624631695)
        ·
          refine ⟨55197432305911689936947543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36798288203941126624631695 55197432305911689936947543)
          ·
            refine ⟨82796148458867534905421315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55197432305911689936947543 82796148458867534905421315)
            ·
              refine ⟨124194222688301302358131973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82796148458867534905421315 124194222688301302358131973)
              ·
                refine ⟨23286416754056494192149745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124194222688301302358131973 23286416754056494192149745)
                ·
                  refine ⟨17464812565542370644112309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23286416754056494192149745 17464812565542370644112309)
                  ·
                    refine ⟨1637326178019597247885529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17464812565542370644112309 1637326178019597247885529)
                    ·
                      refine ⟨1227994633514697935914147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1637326178019597247885529 1227994633514697935914147)
                      ·
                        rfl

theorem cell23_2391511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_2391511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391511 prefixEnd_2391511 := by exact prefixLift 2391511
  have htrace : WordTrace (prefixWord ++ tailWord_2391511) baseStart_2391511 baseEnd_2391511 := by
    simpa [prefixWord, tailWord_2391511, baseEnd_2391511] using wordTrace_append hprefix tailTrace_2391511
  have hstable : (prefixWord ++ tailWord_2391511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391511).length < 2 ^ (prefixWord ++ tailWord_2391511).sum := by decide
  have hdescent : baseEnd_2391511 < baseStart_2391511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391525 : List Nat := [1, 3, 1, 5, 1, 3, 1, 3, 5]
def baseStart_2391525 : Nat := 118140960795 + 2391525 * 2 ^ 59
def prefixEnd_2391525 : Nat := 4983230072969 + 3 ^ 40 * 2391525 * 2
def baseEnd_2391525 : Nat := 136444646915984542348787

theorem tailTrace_2391525 : CollatzResearch.WordTrace tailWord_2391525 prefixEnd_2391525 136444646915984542348787 := by
  unfold tailWord_2391525
  simp only [CollatzResearch.WordTrace]
  refine ⟨87226082660920839797544029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58150721773947226531696019 87226082660920839797544029)
  ·
    refine ⟨32709780997845314924079011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87226082660920839797544029 32709780997845314924079011)
    ·
      refine ⟨49064671496767972386118517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32709780997845314924079011 49064671496767972386118517)
      ·
        refine ⟨4599812952821997411198611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49064671496767972386118517 4599812952821997411198611)
        ·
          refine ⟨6899719429232996116797917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4599812952821997411198611 6899719429232996116797917)
          ·
            refine ⟨2587394785962373543799219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6899719429232996116797917 2587394785962373543799219)
            ·
              refine ⟨3881092178943560315698829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2587394785962373543799219 3881092178943560315698829)
              ·
                refine ⟨1455409567103835118387061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3881092178943560315698829 1455409567103835118387061)
                ·
                  refine ⟨136444646915984542348787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1455409567103835118387061 136444646915984542348787)
                  ·
                    rfl

theorem cell23_2391525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_2391525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391525 prefixEnd_2391525 := by exact prefixLift 2391525
  have htrace : WordTrace (prefixWord ++ tailWord_2391525) baseStart_2391525 baseEnd_2391525 := by
    simpa [prefixWord, tailWord_2391525, baseEnd_2391525] using wordTrace_append hprefix tailTrace_2391525
  have hstable : (prefixWord ++ tailWord_2391525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391525).length < 2 ^ (prefixWord ++ tailWord_2391525).sum := by decide
  have hdescent : baseEnd_2391525 < baseStart_2391525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391538 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_2391538 : Nat := 118140960795 + 2391538 * 2 ^ 59
def prefixEnd_2391538 : Nat := 4983230072969 + 3 ^ 40 * 2391538 * 2
def baseEnd_2391538 : Nat := 409336165830789776758841

theorem tailTrace_2391538 : CollatzResearch.WordTrace tailWord_2391538 prefixEnd_2391538 409336165830789776758841 := by
  unfold tailWord_2391538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21806639202468435754441817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58151037873249162011844845 21806639202468435754441817)
  ·
    refine ⟨16354979401851326815831363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21806639202468435754441817 16354979401851326815831363)
    ·
      refine ⟨24532469102776990223747045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16354979401851326815831363 24532469102776990223747045)
      ·
        refine ⟨4599837956770685666952571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24532469102776990223747045 4599837956770685666952571)
        ·
          refine ⟨6899756935156028500428857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4599837956770685666952571 6899756935156028500428857)
          ·
            refine ⟨5174817701367021375321643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6899756935156028500428857 5174817701367021375321643)
            ·
              refine ⟨7762226552050532062982465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5174817701367021375321643 7762226552050532062982465)
              ·
                refine ⟨5821669914037899047236849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7762226552050532062982465 5821669914037899047236849)
                ·
                  refine ⟨4366252435528424285427637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5821669914037899047236849 4366252435528424285427637)
                  ·
                    refine ⟨409336165830789776758841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4366252435528424285427637 409336165830789776758841)
                    ·
                      rfl

theorem cell23_2391538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_2391538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391538 prefixEnd_2391538 := by exact prefixLift 2391538
  have htrace : WordTrace (prefixWord ++ tailWord_2391538) baseStart_2391538 baseEnd_2391538 := by
    simpa [prefixWord, tailWord_2391538, baseEnd_2391538] using wordTrace_append hprefix tailTrace_2391538
  have hstable : (prefixWord ++ tailWord_2391538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391538).length < 2 ^ (prefixWord ++ tailWord_2391538).sum := by decide
  have hdescent : baseEnd_2391538 < baseStart_2391538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391551 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 3, 4]
def baseStart_2391551 : Nat := 118140960795 + 2391551 * 2 ^ 59
def prefixEnd_2391551 : Nat := 4983230072969 + 3 ^ 40 * 2391551 * 2
def baseEnd_2391551 : Nat := 409338390913625926471321

theorem tailTrace_2391551 : CollatzResearch.WordTrace tailWord_2391551 prefixEnd_2391551 409338390913625926471321 := by
  unfold tailWord_2391551
  simp only [CollatzResearch.WordTrace]
  refine ⟨87227030958826646237990507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58151353972551097491993671 87227030958826646237990507)
  ·
    refine ⟨130840546438239969356985761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87227030958826646237990507 130840546438239969356985761)
    ·
      refine ⟨98130409828679977017739321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130840546438239969356985761 98130409828679977017739321)
      ·
        refine ⟨73597807371509982763304491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98130409828679977017739321 73597807371509982763304491)
        ·
          refine ⟨110396711057264974144956737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73597807371509982763304491 110396711057264974144956737)
          ·
            refine ⟨82797533292948730608717553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110396711057264974144956737 82797533292948730608717553)
            ·
              refine ⟨62098149969711547956538165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82797533292948730608717553 62098149969711547956538165)
              ·
                refine ⟨5821701559660457620925453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62098149969711547956538165 5821701559660457620925453)
                ·
                  refine ⟨2183138084872671607847045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5821701559660457620925453 2183138084872671607847045)
                  ·
                    refine ⟨409338390913625926471321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2183138084872671607847045 409338390913625926471321)
                    ·
                      rfl

theorem cell23_2391551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 4].length) (baseStart_2391551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391551 prefixEnd_2391551 := by exact prefixLift 2391551
  have htrace : WordTrace (prefixWord ++ tailWord_2391551) baseStart_2391551 baseEnd_2391551 := by
    simpa [prefixWord, tailWord_2391551, baseEnd_2391551] using wordTrace_append hprefix tailTrace_2391551
  have hstable : (prefixWord ++ tailWord_2391551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391551).length < 2 ^ (prefixWord ++ tailWord_2391551).sum := by decide
  have hdescent : baseEnd_2391551 < baseStart_2391551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391561 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 4, 2, 3]
def baseStart_2391561 : Nat := 118140960795 + 2391561 * 2 ^ 59
def prefixEnd_2391561 : Nat := 4983230072969 + 3 ^ 40 * 2391561 * 2
def baseEnd_2391561 : Nat := 1228020307547422740288917

theorem tailTrace_2391561 : CollatzResearch.WordTrace tailWord_2391561 prefixEnd_2391561 1228020307547422740288917 := by
  unfold tailWord_2391561
  simp only [CollatzResearch.WordTrace]
  refine ⟨87227395688790417945854537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58151597125860278630569691 87227395688790417945854537)
  ·
    refine ⟨65420546766592813459390903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87227395688790417945854537 65420546766592813459390903)
    ·
      refine ⟨98130820149889220189086355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65420546766592813459390903 98130820149889220189086355)
      ·
        refine ⟨147196230224833830283629533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98130820149889220189086355 147196230224833830283629533)
        ·
          refine ⟨55198586334312686356361075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147196230224833830283629533 55198586334312686356361075)
          ·
            refine ⟨82797879501469029534541613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55198586334312686356361075 82797879501469029534541613)
            ·
              refine ⟨31049204813050886075453105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82797879501469029534541613 31049204813050886075453105)
              ·
                refine ⟨23286903609788164556589829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31049204813050886075453105 23286903609788164556589829)
                ·
                  refine ⟨4366294426835280854360593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23286903609788164556589829 4366294426835280854360593)
                  ·
                    refine ⟨3274720820126460640770445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4366294426835280854360593 3274720820126460640770445)
                    ·
                      refine ⟨1228020307547422740288917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3274720820126460640770445 1228020307547422740288917)
                      ·
                        rfl

theorem cell23_2391561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2, 3].length) (baseStart_2391561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391561 prefixEnd_2391561 := by exact prefixLift 2391561
  have htrace : WordTrace (prefixWord ++ tailWord_2391561) baseStart_2391561 baseEnd_2391561 := by
    simpa [prefixWord, tailWord_2391561, baseEnd_2391561] using wordTrace_append hprefix tailTrace_2391561
  have hstable : (prefixWord ++ tailWord_2391561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391561).length < 2 ^ (prefixWord ++ tailWord_2391561).sum := by decide
  have hdescent : baseEnd_2391561 < baseStart_2391561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391598 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_2391598 : Nat := 118140960795 + 2391598 * 2 ^ 59
def prefixEnd_2391598 : Nat := 4983230072969 + 3 ^ 40 * 2391598 * 2
def baseEnd_2391598 : Nat := 136448811814626566169583

theorem tailTrace_2391598 : CollatzResearch.WordTrace tailWord_2391598 prefixEnd_2391598 136448811814626566169583 := by
  unfold tailWord_2391598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10903593148707046658118931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58152496793104248843300965 10903593148707046658118931)
  ·
    refine ⟨16355389723060569987178397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10903593148707046658118931 16355389723060569987178397)
    ·
      refine ⟨6133271146147713745191899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16355389723060569987178397 6133271146147713745191899)
      ·
        refine ⟨9199906719221570617787849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6133271146147713745191899 9199906719221570617787849)
        ·
          refine ⟨6899930039416177963340887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9199906719221570617787849 6899930039416177963340887)
          ·
            refine ⟨10349895059124266945011331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6899930039416177963340887 10349895059124266945011331)
            ·
              refine ⟨15524842588686400417516997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10349895059124266945011331 15524842588686400417516997)
              ·
                refine ⟨2910907985378700078284437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15524842588686400417516997 2910907985378700078284437)
                ·
                  refine ⟨136448811814626566169583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2910907985378700078284437 136448811814626566169583)
                  ·
                    rfl

theorem cell23_2391598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_2391598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391598 prefixEnd_2391598 := by exact prefixLift 2391598
  have htrace : WordTrace (prefixWord ++ tailWord_2391598) baseStart_2391598 baseEnd_2391598 := by
    simpa [prefixWord, tailWord_2391598, baseEnd_2391598] using wordTrace_append hprefix tailTrace_2391598
  have hstable : (prefixWord ++ tailWord_2391598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391598).length < 2 ^ (prefixWord ++ tailWord_2391598).sum := by decide
  have hdescent : baseEnd_2391598 < baseStart_2391598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391629 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_2391629 : Nat := 118140960795 + 2391629 * 2 ^ 59
def prefixEnd_2391629 : Nat := 4983230072969 + 3 ^ 40 * 2391629 * 2
def baseEnd_2391629 : Nat := 1228055224231928474238605

theorem tailTrace_2391629 : CollatzResearch.WordTrace tailWord_2391629 prefixEnd_2391629 1228055224231928474238605 := by
  unfold tailWord_2391629
  simp only [CollatzResearch.WordTrace]
  refine ⟨87229875852544065559329941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58153250568362710372886627 87229875852544065559329941)
  ·
    refine ⟨4088900430588003073093591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87229875852544065559329941 4088900430588003073093591)
    ·
      refine ⟨6133350645882004609640387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4088900430588003073093591 6133350645882004609640387)
      ·
        refine ⟨9200025968823006914460581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6133350645882004609640387 9200025968823006914460581)
        ·
          refine ⟨1725004869154313796461359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9200025968823006914460581 1725004869154313796461359)
          ·
            refine ⟨2587507303731470694692039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725004869154313796461359 2587507303731470694692039)
            ·
              refine ⟨3881260955597206042038059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2587507303731470694692039 3881260955597206042038059)
              ·
                refine ⟨5821891433395809063057089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3881260955597206042038059 5821891433395809063057089)
                ·
                  refine ⟨4366418575046856797292817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5821891433395809063057089 4366418575046856797292817)
                  ·
                    refine ⟨3274813931285142597969613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4366418575046856797292817 3274813931285142597969613)
                    ·
                      refine ⟨1228055224231928474238605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3274813931285142597969613 1228055224231928474238605)
                      ·
                        rfl

theorem cell23_2391629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_2391629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391629 prefixEnd_2391629 := by exact prefixLift 2391629
  have htrace : WordTrace (prefixWord ++ tailWord_2391629) baseStart_2391629 baseEnd_2391629 := by
    simpa [prefixWord, tailWord_2391629, baseEnd_2391629] using wordTrace_append hprefix tailTrace_2391629
  have hstable : (prefixWord ++ tailWord_2391629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391629).length < 2 ^ (prefixWord ++ tailWord_2391629).sum := by decide
  have hdescent : baseEnd_2391629 < baseStart_2391629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391675 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 2, 4]
def baseStart_2391675 : Nat := 118140960795 + 2391675 * 2 ^ 59
def prefixEnd_2391675 : Nat := 4983230072969 + 3 ^ 40 * 2391675 * 2
def baseEnd_2391675 : Nat := 409359614780678431421131

theorem tailTrace_2391675 : CollatzResearch.WordTrace tailWord_2391675 prefixEnd_2391675 409359614780678431421131 := by
  unfold tailWord_2391675
  simp only [CollatzResearch.WordTrace]
  refine ⟨87231553610377415415504479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58154369073584943610336319 87231553610377415415504479)
  ·
    refine ⟨130847330415566123123256719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87231553610377415415504479 130847330415566123123256719)
    ·
      refine ⟨196270995623349184684885079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130847330415566123123256719 196270995623349184684885079)
      ·
        refine ⟨294406493435023777027327619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196270995623349184684885079 294406493435023777027327619)
        ·
          refine ⟨441609740152535665540991429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294406493435023777027327619 441609740152535665540991429)
          ·
            refine ⟨82801826278600437288935893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 441609740152535665540991429 82801826278600437288935893)
            ·
              refine ⟨1940667803404697748959435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 82801826278600437288935893 1940667803404697748959435)
              ·
                refine ⟨2911001705107046623439153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940667803404697748959435 2911001705107046623439153)
                ·
                  refine ⟨2183251278830284967579365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2911001705107046623439153 2183251278830284967579365)
                  ·
                    refine ⟨409359614780678431421131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2183251278830284967579365 409359614780678431421131)
                    ·
                      rfl

theorem cell23_2391675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 2, 4].length) (baseStart_2391675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391675 prefixEnd_2391675 := by exact prefixLift 2391675
  have htrace : WordTrace (prefixWord ++ tailWord_2391675) baseStart_2391675 baseEnd_2391675 := by
    simpa [prefixWord, tailWord_2391675, baseEnd_2391675] using wordTrace_append hprefix tailTrace_2391675
  have hstable : (prefixWord ++ tailWord_2391675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391675).length < 2 ^ (prefixWord ++ tailWord_2391675).sum := by decide
  have hdescent : baseEnd_2391675 < baseStart_2391675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391685 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 1, 2, 3]
def baseStart_2391685 : Nat := 118140960795 + 2391685 * 2 ^ 59
def prefixEnd_2391685 : Nat := 4983230072969 + 3 ^ 40 * 2391685 * 2
def baseEnd_2391685 : Nat := 1228083979148580255138347

theorem tailTrace_2391685 : CollatzResearch.WordTrace tailWord_2391685 prefixEnd_2391685 1228083979148580255138347 := by
  unfold tailWord_2391685
  simp only [CollatzResearch.WordTrace]
  refine ⟨87231918340341187123368509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58154612226894124748912339 87231918340341187123368509)
  ·
    refine ⟨32711969377627945171263191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87231918340341187123368509 32711969377627945171263191)
    ·
      refine ⟨49067954066441917756894787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32711969377627945171263191 49067954066441917756894787)
      ·
        refine ⟨73601931099662876635342181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49067954066441917756894787 73601931099662876635342181)
        ·
          refine ⟨13800362081186789369126659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73601931099662876635342181 13800362081186789369126659)
          ·
            refine ⟨20700543121780184053689989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13800362081186789369126659 20700543121780184053689989)
            ·
              refine ⟨3881351835333784510066873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20700543121780184053689989 3881351835333784510066873)
              ·
                refine ⟨2911013876500338382550155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3881351835333784510066873 2911013876500338382550155)
                ·
                  refine ⟨4366520814750507573825233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911013876500338382550155 4366520814750507573825233)
                  ·
                    refine ⟨3274890611062880680368925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4366520814750507573825233 3274890611062880680368925)
                    ·
                      refine ⟨1228083979148580255138347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3274890611062880680368925 1228083979148580255138347)
                      ·
                        rfl

theorem cell23_2391685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_2391685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391685 prefixEnd_2391685 := by exact prefixLift 2391685
  have htrace : WordTrace (prefixWord ++ tailWord_2391685) baseStart_2391685 baseEnd_2391685 := by
    simpa [prefixWord, tailWord_2391685, baseEnd_2391685] using wordTrace_append hprefix tailTrace_2391685
  have hstable : (prefixWord ++ tailWord_2391685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391685).length < 2 ^ (prefixWord ++ tailWord_2391685).sum := by decide
  have hdescent : baseEnd_2391685 < baseStart_2391685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391715 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 2, 1, 3]
def baseStart_2391715 : Nat := 118140960795 + 2391715 * 2 ^ 59
def prefixEnd_2391715 : Nat := 4983230072969 + 3 ^ 40 * 2391715 * 2
def baseEnd_2391715 : Nat := 1228099383568215137763209

theorem tailTrace_2391715 : CollatzResearch.WordTrace tailWord_2391715 prefixEnd_2391715 1228099383568215137763209 := by
  unfold tailWord_2391715
  simp only [CollatzResearch.WordTrace]
  refine ⟨87233012530232502246960599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58155341686821668164640399 87233012530232502246960599)
  ·
    refine ⟨130849518795348753370440899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87233012530232502246960599 130849518795348753370440899)
    ·
      refine ⟨196274278193023130055661349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130849518795348753370440899 196274278193023130055661349)
      ·
        refine ⟨36801427161191836885436503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196274278193023130055661349 36801427161191836885436503)
        ·
          refine ⟨55202140741787755328154755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36801427161191836885436503 55202140741787755328154755)
          ·
            refine ⟨82803211112681632992232133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55202140741787755328154755 82803211112681632992232133)
            ·
              refine ⟨15525602083627806186043525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82803211112681632992232133 15525602083627806186043525)
              ·
                refine ⟨2911050390680213659883161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15525602083627806186043525 2911050390680213659883161)
                ·
                  refine ⟨2183287793010160244912371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2911050390680213659883161 2183287793010160244912371)
                  ·
                    refine ⟨3274931689515240367368557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2183287793010160244912371 3274931689515240367368557)
                    ·
                      refine ⟨1228099383568215137763209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3274931689515240367368557 1228099383568215137763209)
                      ·
                        rfl

theorem cell23_2391715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_2391715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391715 prefixEnd_2391715 := by exact prefixLift 2391715
  have htrace : WordTrace (prefixWord ++ tailWord_2391715) baseStart_2391715 baseEnd_2391715 := by
    simpa [prefixWord, tailWord_2391715, baseEnd_2391715] using wordTrace_append hprefix tailTrace_2391715
  have hstable : (prefixWord ++ tailWord_2391715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391715).length < 2 ^ (prefixWord ++ tailWord_2391715).sum := by decide
  have hdescent : baseEnd_2391715 < baseStart_2391715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391716 : List Nat := [2, 3, 1, 2, 2, 3, 3, 2, 1, 2, 2]
def baseStart_2391716 : Nat := 118140960795 + 2391716 * 2 ^ 59
def prefixEnd_2391716 : Nat := 4983230072969 + 3 ^ 40 * 2391716 * 2
def baseEnd_2391716 : Nat := 1228099897048869633850705

theorem tailTrace_2391716 : CollatzResearch.WordTrace tailWord_2391716 prefixEnd_2391716 1228099897048869633850705 := by
  unfold tailWord_2391716
  simp only [CollatzResearch.WordTrace]
  refine ⟨43616524501614439708873501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58155366002152586278498001 43616524501614439708873501)
  ·
    refine ⟨16356196688105414890827563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43616524501614439708873501 16356196688105414890827563)
    ·
      refine ⟨24534295032158122336241345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16356196688105414890827563 24534295032158122336241345)
      ·
        refine ⟨18400721274118591752181009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24534295032158122336241345 18400721274118591752181009)
        ·
          refine ⟨13800540955588943814135757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18400721274118591752181009 13800540955588943814135757)
          ·
            refine ⟨5175202858345853930300909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13800540955588943814135757 5175202858345853930300909)
            ·
              refine ⟨1940701071879695223862841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5175202858345853930300909 1940701071879695223862841)
              ·
                refine ⟨1455525803909771417897131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1940701071879695223862841 1455525803909771417897131)
                ·
                  refine ⟨2183288705864657126845697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455525803909771417897131 2183288705864657126845697)
                  ·
                    refine ⟨1637466529398492845134273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2183288705864657126845697 1637466529398492845134273)
                    ·
                      refine ⟨1228099897048869633850705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1637466529398492845134273 1228099897048869633850705)
                      ·
                        rfl

theorem cell23_2391716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_2391716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391716 prefixEnd_2391716 := by exact prefixLift 2391716
  have htrace : WordTrace (prefixWord ++ tailWord_2391716) baseStart_2391716 baseEnd_2391716 := by
    simpa [prefixWord, tailWord_2391716, baseEnd_2391716] using wordTrace_append hprefix tailTrace_2391716
  have hstable : (prefixWord ++ tailWord_2391716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391716).length < 2 ^ (prefixWord ++ tailWord_2391716).sum := by decide
  have hdescent : baseEnd_2391716 < baseStart_2391716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391726 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2391726 : Nat := 118140960795 + 2391726 * 2 ^ 59
def prefixEnd_2391726 : Nat := 4983230072969 + 3 ^ 40 * 2391726 * 2
def baseEnd_2391726 : Nat := 409368343951804864908553

theorem tailTrace_2391726 : CollatzResearch.WordTrace tailWord_2391726 prefixEnd_2391726 409368343951804864908553 := by
  unfold tailWord_2391726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10904176716649081390701379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58155609155461767417074021 10904176716649081390701379)
  ·
    refine ⟨16356265074973622086052069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10904176716649081390701379 16356265074973622086052069)
    ·
      refine ⟨3066799701557554141134763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16356265074973622086052069 3066799701557554141134763)
      ·
        refine ⟨4600199552336331211702145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3066799701557554141134763 4600199552336331211702145)
        ·
          refine ⟨3450149664252248408776609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4600199552336331211702145 3450149664252248408776609)
          ·
            refine ⟨2587612248189186306582457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3450149664252248408776609 2587612248189186306582457)
            ·
              refine ⟨1940709186141889729936843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2587612248189186306582457 1940709186141889729936843)
              ·
                refine ⟨2911063779212834594905265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940709186141889729936843 2911063779212834594905265)
                ·
                  refine ⟨2183297834409625946178949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2911063779212834594905265 2183297834409625946178949)
                  ·
                    refine ⟨409368343951804864908553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2183297834409625946178949 409368343951804864908553)
                    ·
                      rfl

theorem cell23_2391726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2391726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391726 prefixEnd_2391726 := by exact prefixLift 2391726
  have htrace : WordTrace (prefixWord ++ tailWord_2391726) baseStart_2391726 baseEnd_2391726 := by
    simpa [prefixWord, tailWord_2391726, baseEnd_2391726] using wordTrace_append hprefix tailTrace_2391726
  have hstable : (prefixWord ++ tailWord_2391726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391726).length < 2 ^ (prefixWord ++ tailWord_2391726).sum := by decide
  have hdescent : baseEnd_2391726 < baseStart_2391726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391731 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 1, 8]
def baseStart_2391731 : Nat := 118140960795 + 2391731 * 2 ^ 59
def prefixEnd_2391731 : Nat := 4983230072969 + 3 ^ 40 * 2391731 * 2
def baseEnd_2391731 : Nat := 409369199752895691721045

theorem tailTrace_2391731 : CollatzResearch.WordTrace tailWord_2391731 prefixEnd_2391731 409369199752895691721045 := by
  unfold tailWord_2391731
  simp only [CollatzResearch.WordTrace]
  refine ⟨87233596098174536979543047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58155730732116357986362031 87233596098174536979543047)
  ·
    refine ⟨130850394147261805469314571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87233596098174536979543047 130850394147261805469314571)
    ·
      refine ⟨196275591220892708203971857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130850394147261805469314571 196275591220892708203971857)
      ·
        refine ⟨147206693415669531152978893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196275591220892708203971857 147206693415669531152978893)
        ·
          refine ⟨55202510030876074182367085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147206693415669531152978893 55202510030876074182367085)
          ·
            refine ⟨20700941261578527818387657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55202510030876074182367085 20700941261578527818387657)
            ·
              refine ⟨15525705946183895863790743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20700941261578527818387657 15525705946183895863790743)
              ·
                refine ⟨23288558919275843795686115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15525705946183895863790743 23288558919275843795686115)
                ·
                  refine ⟨34932838378913765693529173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23288558919275843795686115 34932838378913765693529173)
                  ·
                    refine ⟨409369199752895691721045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34932838378913765693529173 409369199752895691721045)
                    ·
                      rfl

theorem cell23_2391731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 8].length) (baseStart_2391731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391731 prefixEnd_2391731 := by exact prefixLift 2391731
  have htrace : WordTrace (prefixWord ++ tailWord_2391731) baseStart_2391731 baseEnd_2391731 := by
    simpa [prefixWord, tailWord_2391731, baseEnd_2391731] using wordTrace_append hprefix tailTrace_2391731
  have hstable : (prefixWord ++ tailWord_2391731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391731).length < 2 ^ (prefixWord ++ tailWord_2391731).sum := by decide
  have hdescent : baseEnd_2391731 < baseStart_2391731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391742 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_2391742 : Nat := 118140960795 + 2391742 * 2 ^ 59
def prefixEnd_2391742 : Nat := 4983230072969 + 3 ^ 40 * 2391742 * 2
def baseEnd_2391742 : Nat := 1228113247545886532125585

theorem tailTrace_2391742 : CollatzResearch.WordTrace tailWord_2391742 prefixEnd_2391742 1228113247545886532125585 := by
  unfold tailWord_2391742
  simp only [CollatzResearch.WordTrace]
  refine ⟨10904249662641835732274185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58155998200756457238795653 10904249662641835732274185)
  ·
    refine ⟨8178187246981376799205639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10904249662641835732274185 8178187246981376799205639)
    ·
      refine ⟨12267280870472065198808459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8178187246981376799205639 12267280870472065198808459)
      ·
        refine ⟨18400921305708097798212689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12267280870472065198808459 18400921305708097798212689)
        ·
          refine ⟨13800690979281073348659517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18400921305708097798212689 13800690979281073348659517)
          ·
            refine ⟨5175259117230402505747319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13800690979281073348659517 5175259117230402505747319)
            ·
              refine ⟨7762888675845603758620979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5175259117230402505747319 7762888675845603758620979)
              ·
                refine ⟨11644333013768405637931469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7762888675845603758620979 11644333013768405637931469)
                ·
                  refine ⟨4366624880163152114224301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11644333013768405637931469 4366624880163152114224301)
                  ·
                    refine ⟨1637484330061182042834113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4366624880163152114224301 1637484330061182042834113)
                    ·
                      refine ⟨1228113247545886532125585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1637484330061182042834113 1228113247545886532125585)
                      ·
                        rfl

theorem cell23_2391742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_2391742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391742 prefixEnd_2391742 := by exact prefixLift 2391742
  have htrace : WordTrace (prefixWord ++ tailWord_2391742) baseStart_2391742 baseEnd_2391742 := by
    simpa [prefixWord, tailWord_2391742, baseEnd_2391742] using wordTrace_append hprefix tailTrace_2391742
  have hstable : (prefixWord ++ tailWord_2391742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391742).length < 2 ^ (prefixWord ++ tailWord_2391742).sum := by decide
  have hdescent : baseEnd_2391742 < baseStart_2391742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391755 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 6, 2, 2]
def baseStart_2391755 : Nat := 118140960795 + 2391755 * 2 ^ 59
def prefixEnd_2391755 : Nat := 4983230072969 + 3 ^ 40 * 2391755 * 2
def baseEnd_2391755 : Nat := 1228119922794394981263025

theorem tailTrace_2391755 : CollatzResearch.WordTrace tailWord_2391755 prefixEnd_2391755 1228119922794394981263025 := by
  unfold tailWord_2391755
  simp only [CollatzResearch.WordTrace]
  refine ⟨87234471450087589078416719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58156314300058392718944479 87234471450087589078416719)
  ·
    refine ⟨130851707175131383617625079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87234471450087589078416719 130851707175131383617625079)
    ·
      refine ⟨196277560762697075426437619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130851707175131383617625079 196277560762697075426437619)
      ·
        refine ⟨294416341144045613139656429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196277560762697075426437619 294416341144045613139656429)
        ·
          refine ⟨110406127929017104927371161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294416341144045613139656429 110406127929017104927371161)
          ·
            refine ⟨82804595946762828695528371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110406127929017104927371161 82804595946762828695528371)
            ·
              refine ⟨124206893920144243043292557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82804595946762828695528371 124206893920144243043292557)
              ·
                refine ⟨46577585220054091141234709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124206893920144243043292557 46577585220054091141234709)
                ·
                  refine ⟨2183324307190035522245377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46577585220054091141234709 2183324307190035522245377)
                  ·
                    refine ⟨1637493230392526641684033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2183324307190035522245377 1637493230392526641684033)
                    ·
                      refine ⟨1228119922794394981263025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1637493230392526641684033 1228119922794394981263025)
                      ·
                        rfl

theorem cell23_2391755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 2, 2].length) (baseStart_2391755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391755 prefixEnd_2391755 := by exact prefixLift 2391755
  have htrace : WordTrace (prefixWord ++ tailWord_2391755) baseStart_2391755 baseEnd_2391755 := by
    simpa [prefixWord, tailWord_2391755, baseEnd_2391755] using wordTrace_append hprefix tailTrace_2391755
  have hstable : (prefixWord ++ tailWord_2391755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391755).length < 2 ^ (prefixWord ++ tailWord_2391755).sum := by decide
  have hdescent : baseEnd_2391755 < baseStart_2391755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391758 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_2391758 : Nat := 118140960795 + 2391758 * 2 ^ 59
def prefixEnd_2391758 : Nat := 4983230072969 + 3 ^ 40 * 2391758 * 2
def baseEnd_2391758 : Nat := 1228121463236358469525511

theorem tailTrace_2391758 : CollatzResearch.WordTrace tailWord_2391758 prefixEnd_2391758 1228121463236358469525511 := by
  unfold tailWord_2391758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10904322608634590073846991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58156387246051147060517285 10904322608634590073846991)
  ·
    refine ⟨16356483912951885110770487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10904322608634590073846991 16356483912951885110770487)
    ·
      refine ⟨24534725869427827666155731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16356483912951885110770487 24534725869427827666155731)
      ·
        refine ⟨36802088804141741499233597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24534725869427827666155731 36802088804141741499233597)
        ·
          refine ⟨13800783301553153062212599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36802088804141741499233597 13800783301553153062212599)
          ·
            refine ⟨20701174952329729593318899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13800783301553153062212599 20701174952329729593318899)
            ·
              refine ⟨31051762428494594389978349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20701174952329729593318899 31051762428494594389978349)
              ·
                refine ⟨11644410910685472896241881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31051762428494594389978349 11644410910685472896241881)
                ·
                  refine ⟨8733308183014104672181411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11644410910685472896241881 8733308183014104672181411)
                  ·
                    refine ⟨13099962274521157008272117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8733308183014104672181411 13099962274521157008272117)
                    ·
                      refine ⟨1228121463236358469525511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13099962274521157008272117 1228121463236358469525511)
                      ·
                        rfl

theorem cell23_2391758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_2391758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391758 prefixEnd_2391758 := by exact prefixLift 2391758
  have htrace : WordTrace (prefixWord ++ tailWord_2391758) baseStart_2391758 baseEnd_2391758 := by
    simpa [prefixWord, tailWord_2391758, baseEnd_2391758] using wordTrace_append hprefix tailTrace_2391758
  have hstable : (prefixWord ++ tailWord_2391758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391758).length < 2 ^ (prefixWord ++ tailWord_2391758).sum := by decide
  have hdescent : baseEnd_2391758 < baseStart_2391758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391768 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2391768 : Nat := 118140960795 + 2391768 * 2 ^ 59
def prefixEnd_2391768 : Nat := 4983230072969 + 3 ^ 40 * 2391768 * 2
def baseEnd_2391768 : Nat := 1228126598042903430400465

theorem tailTrace_2391768 : CollatzResearch.WordTrace tailWord_2391768 prefixEnd_2391768 1228126598042903430400465 := by
  unfold tailWord_2391768
  simp only [CollatzResearch.WordTrace]
  refine ⟨43617472799520246149319979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58156630399360328199093305 43617472799520246149319979)
  ·
    refine ⟨65426209199280369223979969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43617472799520246149319979 65426209199280369223979969)
    ·
      refine ⟨49069656899460276917984977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65426209199280369223979969 49069656899460276917984977)
      ·
        refine ⟨36802242674595207688488733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49069656899460276917984977 36802242674595207688488733)
        ·
          refine ⟨13800841002973202883183275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36802242674595207688488733 13800841002973202883183275)
          ·
            refine ⟨20701261504459804324774913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13800841002973202883183275 20701261504459804324774913)
            ·
              refine ⟨15525946128344853243581185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20701261504459804324774913 15525946128344853243581185)
              ·
                refine ⟨11644459596258639932685889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15525946128344853243581185 11644459596258639932685889)
                ·
                  refine ⟨8733344697193979949514417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11644459596258639932685889 8733344697193979949514417)
                  ·
                    refine ⟨6550008522895484962135813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8733344697193979949514417 6550008522895484962135813)
                    ·
                      refine ⟨1228126598042903430400465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6550008522895484962135813 1228126598042903430400465)
                      ·
                        rfl

theorem cell23_2391768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2391768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391768 prefixEnd_2391768 := by exact prefixLift 2391768
  have htrace : WordTrace (prefixWord ++ tailWord_2391768) baseStart_2391768 baseEnd_2391768 := by
    simpa [prefixWord, tailWord_2391768, baseEnd_2391768] using wordTrace_append hprefix tailTrace_2391768
  have hstable : (prefixWord ++ tailWord_2391768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391768).length < 2 ^ (prefixWord ++ tailWord_2391768).sum := by decide
  have hdescent : baseEnd_2391768 < baseStart_2391768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391788 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 3]
def baseStart_2391788 : Nat := 118140960795 + 2391788 * 2 ^ 59
def prefixEnd_2391788 : Nat := 4983230072969 + 3 ^ 40 * 2391788 * 2
def baseEnd_2391788 : Nat := 1228136867655993352150373

theorem tailTrace_2391788 : CollatzResearch.WordTrace tailWord_2391788 prefixEnd_2391788 1228136867655993352150373 := by
  unfold tailWord_2391788
  simp only [CollatzResearch.WordTrace]
  refine ⟨43617837529484017857184009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58157116705978690476245345 43617837529484017857184009)
  ·
    refine ⟨32713378147113013392888007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43617837529484017857184009 32713378147113013392888007)
    ·
      refine ⟨49070067220669520089332011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32713378147113013392888007 49070067220669520089332011)
      ·
        refine ⟨73605100831004280133998017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49070067220669520089332011 73605100831004280133998017)
        ·
          refine ⟨55203825623253210100498513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73605100831004280133998017 55203825623253210100498513)
          ·
            refine ⟨41402869217439907575373885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55203825623253210100498513 41402869217439907575373885)
            ·
              refine ⟨15526075956539965340765207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41402869217439907575373885 15526075956539965340765207)
              ·
                refine ⟨23289113934809948011147811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15526075956539965340765207 23289113934809948011147811)
                ·
                  refine ⟨34933670902214922016721717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23289113934809948011147811 34933670902214922016721717)
                  ·
                    refine ⟨3275031647082648939067661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34933670902214922016721717 3275031647082648939067661)
                    ·
                      refine ⟨1228136867655993352150373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3275031647082648939067661 1228136867655993352150373)
                      ·
                        rfl

theorem cell23_2391788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_2391788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391788 prefixEnd_2391788 := by exact prefixLift 2391788
  have htrace : WordTrace (prefixWord ++ tailWord_2391788) baseStart_2391788 baseEnd_2391788 := by
    simpa [prefixWord, tailWord_2391788, baseEnd_2391788] using wordTrace_append hprefix tailTrace_2391788
  have hstable : (prefixWord ++ tailWord_2391788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391788).length < 2 ^ (prefixWord ++ tailWord_2391788).sum := by decide
  have hdescent : baseEnd_2391788 < baseStart_2391788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391789 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_2391789 : Nat := 118140960795 + 2391789 * 2 ^ 59
def prefixEnd_2391789 : Nat := 4983230072969 + 3 ^ 40 * 2391789 * 2
def baseEnd_2391789 : Nat := 1228137381136647848237869

theorem tailTrace_2391789 : CollatzResearch.WordTrace tailWord_2391789 prefixEnd_2391789 1228137381136647848237869 := by
  unfold tailWord_2391789
  simp only [CollatzResearch.WordTrace]
  refine ⟨87235711531964412885154421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58157141021309608590102947 87235711531964412885154421)
  ·
    refine ⟨8178347956121663707983227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87235711531964412885154421 8178347956121663707983227)
    ·
      refine ⟨12267521934182495561974841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8178347956121663707983227 12267521934182495561974841)
      ·
        refine ⟨9200641450636871671481131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12267521934182495561974841 9200641450636871671481131)
        ·
          refine ⟨13800962175955307507221697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9200641450636871671481131 13800962175955307507221697)
          ·
            refine ⟨10350721631966480630416273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13800962175955307507221697 10350721631966480630416273)
            ·
              refine ⟨7763041223974860472812205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10350721631966480630416273 7763041223974860472812205)
              ·
                refine ⟨2911140458990572677304577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7763041223974860472812205 2911140458990572677304577)
                ·
                  refine ⟨2183355344242929507978433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2911140458990572677304577 2183355344242929507978433)
                  ·
                    refine ⟨1637516508182197130983825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2183355344242929507978433 1637516508182197130983825)
                    ·
                      refine ⟨1228137381136647848237869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1637516508182197130983825 1228137381136647848237869)
                      ·
                        rfl

theorem cell23_2391789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_2391789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391789 prefixEnd_2391789 := by exact prefixLift 2391789
  have htrace : WordTrace (prefixWord ++ tailWord_2391789) baseStart_2391789 baseEnd_2391789 := by
    simpa [prefixWord, tailWord_2391789, baseEnd_2391789] using wordTrace_append hprefix tailTrace_2391789
  have hstable : (prefixWord ++ tailWord_2391789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391789).length < 2 ^ (prefixWord ++ tailWord_2391789).sum := by decide
  have hdescent : baseEnd_2391789 < baseStart_2391789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391812 : List Nat := [2, 3, 2, 2, 1, 3, 2, 3, 5]
def baseStart_2391812 : Nat := 118140960795 + 2391812 * 2 ^ 59
def prefixEnd_2391812 : Nat := 4983230072969 + 3 ^ 40 * 2391812 * 2
def baseEnd_2391812 : Nat := 136461021243522362027807

theorem tailTrace_2391812 : CollatzResearch.WordTrace tailWord_2391812 prefixEnd_2391812 136461021243522362027807 := by
  unfold tailWord_2391812
  simp only [CollatzResearch.WordTrace]
  refine ⟨43618275205440543906620845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58157700273920725208827793 43618275205440543906620845)
  ·
    refine ⟨16356853202040203964982817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43618275205440543906620845 16356853202040203964982817)
    ·
      refine ⟨12267639901530152973737113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16356853202040203964982817 12267639901530152973737113)
      ·
        refine ⟨9200729926147614730302835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12267639901530152973737113 9200729926147614730302835)
        ·
          refine ⟨13801094889221422095454253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9200729926147614730302835 13801094889221422095454253)
          ·
            refine ⟨5175410583458033285795345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13801094889221422095454253 5175410583458033285795345)
            ·
              refine ⟨3881557937593524964346509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5175410583458033285795345 3881557937593524964346509)
              ·
                refine ⟨1455584226597571861629941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3881557937593524964346509 1455584226597571861629941)
                ·
                  refine ⟨136461021243522362027807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1455584226597571861629941 136461021243522362027807)
                  ·
                    rfl

theorem cell23_2391812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_2391812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391812 prefixEnd_2391812 := by exact prefixLift 2391812
  have htrace : WordTrace (prefixWord ++ tailWord_2391812) baseStart_2391812 baseEnd_2391812 := by
    simpa [prefixWord, tailWord_2391812, baseEnd_2391812] using wordTrace_append hprefix tailTrace_2391812
  have hstable : (prefixWord ++ tailWord_2391812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391812).length < 2 ^ (prefixWord ++ tailWord_2391812).sum := by decide
  have hdescent : baseEnd_2391812 < baseStart_2391812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391862 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2391862 : Nat := 118140960795 + 2391862 * 2 ^ 59
def prefixEnd_2391862 : Nat := 4983230072969 + 3 ^ 40 * 2391862 * 2
def baseEnd_2391862 : Nat := 1228174865224426062625033

theorem tailTrace_2391862 : CollatzResearch.WordTrace tailWord_2391862 prefixEnd_2391862 1228174865224426062625033 := by
  unfold tailWord_2391862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5452398378793746647035115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58158916040466630901707893 5452398378793746647035115)
  ·
    refine ⟨8178597568190619970552673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5452398378793746647035115 8178597568190619970552673)
    ·
      refine ⟨6133948176142964977914505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8178597568190619970552673 6133948176142964977914505)
      ·
        refine ⟨4600461132107223733435879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6133948176142964977914505 4600461132107223733435879)
        ·
          refine ⟨6900691698160835600153819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4600461132107223733435879 6900691698160835600153819)
          ·
            refine ⟨10351037547241253400230729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6900691698160835600153819 10351037547241253400230729)
            ·
              refine ⟨7763278160430940050173047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10351037547241253400230729 7763278160430940050173047)
              ·
                refine ⟨11644917240646410075259571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7763278160430940050173047 11644917240646410075259571)
                ·
                  refine ⟨17467375860969615112889357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11644917240646410075259571 17467375860969615112889357)
                  ·
                    refine ⟨6550265947863605667333509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17467375860969615112889357 6550265947863605667333509)
                    ·
                      refine ⟨1228174865224426062625033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6550265947863605667333509 1228174865224426062625033)
                      ·
                        rfl

theorem cell23_2391862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2391862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391862 prefixEnd_2391862 := by exact prefixLift 2391862
  have htrace : WordTrace (prefixWord ++ tailWord_2391862) baseStart_2391862 baseEnd_2391862 := by
    simpa [prefixWord, tailWord_2391862, baseEnd_2391862] using wordTrace_append hprefix tailTrace_2391862
  have hstable : (prefixWord ++ tailWord_2391862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391862).length < 2 ^ (prefixWord ++ tailWord_2391862).sum := by decide
  have hdescent : baseEnd_2391862 < baseStart_2391862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391868 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 8]
def baseStart_2391868 : Nat := 118140960795 + 2391868 * 2 ^ 59
def prefixEnd_2391868 : Nat := 4983230072969 + 3 ^ 40 * 2391868 * 2
def baseEnd_2391868 : Nat := 136464216234261448794445

theorem tailTrace_2391868 : CollatzResearch.WordTrace tailWord_2391868 prefixEnd_2391868 136464216234261448794445 := by
  unfold tailWord_2391868
  simp only [CollatzResearch.WordTrace]
  refine ⟨43619296449339104688640129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58159061932452139584853505 43619296449339104688640129)
  ·
    refine ⟨32714472337004328516480097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43619296449339104688640129 32714472337004328516480097)
    ·
      refine ⟨24535854252753246387360073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32714472337004328516480097 24535854252753246387360073)
      ·
        refine ⟨18401890689564934790520055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24535854252753246387360073 18401890689564934790520055)
        ·
          refine ⟨27602836034347402185780083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18401890689564934790520055 27602836034347402185780083)
          ·
            refine ⟨41404254051521103278670125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27602836034347402185780083 41404254051521103278670125)
            ·
              refine ⟨15526595269320413729501297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41404254051521103278670125 15526595269320413729501297)
              ·
                refine ⟨11644946451990310297125973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15526595269320413729501297 11644946451990310297125973)
                ·
                  refine ⟨136464216234261448794445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11644946451990310297125973 136464216234261448794445)
                  ·
                    rfl

theorem cell23_2391868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_2391868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391868 prefixEnd_2391868 := by exact prefixLift 2391868
  have htrace : WordTrace (prefixWord ++ tailWord_2391868) baseStart_2391868 baseEnd_2391868 := by
    simpa [prefixWord, tailWord_2391868, baseEnd_2391868] using wordTrace_append hprefix tailTrace_2391868
  have hstable : (prefixWord ++ tailWord_2391868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391868).length < 2 ^ (prefixWord ++ tailWord_2391868).sum := by decide
  have hdescent : baseEnd_2391868 < baseStart_2391868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391912 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_2391912 : Nat := 118140960795 + 2391912 * 2 ^ 59
def prefixEnd_2391912 : Nat := 4983230072969 + 3 ^ 40 * 2391912 * 2
def baseEnd_2391912 : Nat := 1228200539257150866999803

theorem tailTrace_2391912 : CollatzResearch.WordTrace tailWord_2391912 prefixEnd_2391912 1228200539257150866999803 := by
  unfold tailWord_2391912
  simp only [CollatzResearch.WordTrace]
  refine ⟨43620098855259402445940995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58160131807012536594587993 43620098855259402445940995)
  ·
    refine ⟨65430148282889103668911493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43620098855259402445940995 65430148282889103668911493)
    ·
      refine ⟨12268152803041706937920905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65430148282889103668911493 12268152803041706937920905)
      ·
        refine ⟨9201114602281280203440679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12268152803041706937920905 9201114602281280203440679)
        ·
          refine ⟨13801671903421920305161019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9201114602281280203440679 13801671903421920305161019)
          ·
            refine ⟨20702507855132880457741529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13801671903421920305161019 20702507855132880457741529)
            ·
              refine ⟨15526880891349660343306147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20702507855132880457741529 15526880891349660343306147)
              ·
                refine ⟨23290321337024490514959221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15526880891349660343306147 23290321337024490514959221)
                ·
                  refine ⟨2183467625346045985777427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23290321337024490514959221 2183467625346045985777427)
                  ·
                    refine ⟨3275201438019068978666141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2183467625346045985777427 3275201438019068978666141)
                    ·
                      refine ⟨1228200539257150866999803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3275201438019068978666141 1228200539257150866999803)
                      ·
                        rfl

theorem cell23_2391912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_2391912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391912 prefixEnd_2391912 := by exact prefixLift 2391912
  have htrace : WordTrace (prefixWord ++ tailWord_2391912) baseStart_2391912 baseEnd_2391912 := by
    simpa [prefixWord, tailWord_2391912, baseEnd_2391912] using wordTrace_append hprefix tailTrace_2391912
  have hstable : (prefixWord ++ tailWord_2391912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391912).length < 2 ^ (prefixWord ++ tailWord_2391912).sum := by decide
  have hdescent : baseEnd_2391912 < baseStart_2391912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391929 : List Nat := [1, 2, 1, 3, 2, 2, 2, 5, 1, 1, 3]
def baseStart_2391929 : Nat := 118140960795 + 2391929 * 2 ^ 59
def prefixEnd_2391929 : Nat := 4983230072969 + 3 ^ 40 * 2391929 * 2
def baseEnd_2391929 : Nat := 1228209268428277300487225

theorem tailTrace_2391929 : CollatzResearch.WordTrace tailWord_2391929 prefixEnd_2391929 1228209268428277300487225 := by
  unfold tailWord_2391929
  simp only [CollatzResearch.WordTrace]
  refine ⟨87240817751457216795250841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58160545167638144530167227 87240817751457216795250841)
  ·
    refine ⟨65430613313592912596438131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87240817751457216795250841 65430613313592912596438131)
    ·
      refine ⟨98145919970389368894657197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65430613313592912596438131 98145919970389368894657197)
      ·
        refine ⟨36804719988896013335496449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98145919970389368894657197 36804719988896013335496449)
        ·
          refine ⟨27603539991672010001622337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36804719988896013335496449 27603539991672010001622337)
          ·
            refine ⟨20702654993754007501216753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27603539991672010001622337 20702654993754007501216753)
            ·
              refine ⟨15526991245315505625912565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20702654993754007501216753 15526991245315505625912565)
              ·
                refine ⟨1455655429248328652429303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15526991245315505625912565 1455655429248328652429303)
                ·
                  refine ⟨2183483143872492978643955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455655429248328652429303 2183483143872492978643955)
                  ·
                    refine ⟨3275224715808739467965933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2183483143872492978643955 3275224715808739467965933)
                    ·
                      refine ⟨1228209268428277300487225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3275224715808739467965933 1228209268428277300487225)
                      ·
                        rfl

theorem cell23_2391929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_2391929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391929 prefixEnd_2391929 := by exact prefixLift 2391929
  have htrace : WordTrace (prefixWord ++ tailWord_2391929) baseStart_2391929 baseEnd_2391929 := by
    simpa [prefixWord, tailWord_2391929, baseEnd_2391929] using wordTrace_append hprefix tailTrace_2391929
  have hstable : (prefixWord ++ tailWord_2391929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391929).length < 2 ^ (prefixWord ++ tailWord_2391929).sum := by decide
  have hdescent : baseEnd_2391929 < baseStart_2391929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391962 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 1, 6]
def baseStart_2391962 : Nat := 118140960795 + 2391962 * 2 ^ 59
def prefixEnd_2391962 : Nat := 4983230072969 + 3 ^ 40 * 2391962 * 2
def baseEnd_2391962 : Nat := 409408737763291890458191

theorem tailTrace_2391962 : CollatzResearch.WordTrace tailWord_2391962 prefixEnd_2391962 409408737763291890458191 := by
  unfold tailWord_2391962
  simp only [CollatzResearch.WordTrace]
  refine ⟨21810505340084415857800535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58161347573558442287468093 21810505340084415857800535)
  ·
    refine ⟨32715758010126623786700803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21810505340084415857800535 32715758010126623786700803)
    ·
      refine ⟨49073637015189935680051205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32715758010126623786700803 49073637015189935680051205)
      ·
        refine ⟨9201306940348112940009601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49073637015189935680051205 9201306940348112940009601)
        ·
          refine ⟨6900980205261084705007201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9201306940348112940009601 6900980205261084705007201)
          ·
            refine ⟨5175735153945813528755401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6900980205261084705007201 5175735153945813528755401)
            ·
              refine ⟨3881801365459360146566551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5175735153945813528755401 3881801365459360146566551)
              ·
                refine ⟨5822702048189040219849827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3881801365459360146566551 5822702048189040219849827)
                ·
                  refine ⟨8734053072283560329774741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5822702048189040219849827 8734053072283560329774741)
                  ·
                    refine ⟨409408737763291890458191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8734053072283560329774741 409408737763291890458191)
                    ·
                      rfl

theorem cell23_2391962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_2391962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391962 prefixEnd_2391962 := by exact prefixLift 2391962
  have htrace : WordTrace (prefixWord ++ tailWord_2391962) baseStart_2391962 baseEnd_2391962 := by
    simpa [prefixWord, tailWord_2391962, baseEnd_2391962] using wordTrace_append hprefix tailTrace_2391962
  have hstable : (prefixWord ++ tailWord_2391962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391962).length < 2 ^ (prefixWord ++ tailWord_2391962).sum := by decide
  have hdescent : baseEnd_2391962 < baseStart_2391962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391972 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_2391972 : Nat := 118140960795 + 2391972 * 2 ^ 59
def prefixEnd_2391972 : Nat := 4983230072969 + 3 ^ 40 * 2391972 * 2
def baseEnd_2391972 : Nat := 1228231348096420632249527

theorem tailTrace_2391972 : CollatzResearch.WordTrace tailWord_2391972 prefixEnd_2391972 1228231348096420632249527 := by
  unfold tailWord_2391972
  simp only [CollatzResearch.WordTrace]
  refine ⟨43621193045150717569533085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58161590726867623426044113 43621193045150717569533085)
  ·
    refine ⟨16357947391931519088574907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43621193045150717569533085 16357947391931519088574907)
    ·
      refine ⟨24536921087897278632862361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16357947391931519088574907 24536921087897278632862361)
      ·
        refine ⟨18402690815922958974646771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24536921087897278632862361 18402690815922958974646771)
        ·
          refine ⟨27604036223884438461970157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18402690815922958974646771 27604036223884438461970157)
          ·
            refine ⟨10351513583956664423238809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27604036223884438461970157 10351513583956664423238809)
            ·
              refine ⟨7763635187967498317429107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10351513583956664423238809 7763635187967498317429107)
              ·
                refine ⟨11645452781951247476143661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7763635187967498317429107 11645452781951247476143661)
                ·
                  refine ⟨4367044793231717803553873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11645452781951247476143661 4367044793231717803553873)
                  ·
                    refine ⟨3275283594923788352665405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4367044793231717803553873 3275283594923788352665405)
                    ·
                      refine ⟨1228231348096420632249527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3275283594923788352665405 1228231348096420632249527)
                      ·
                        rfl

theorem cell23_2391972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_2391972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391972 prefixEnd_2391972 := by exact prefixLift 2391972
  have htrace : WordTrace (prefixWord ++ tailWord_2391972) baseStart_2391972 baseEnd_2391972 := by
    simpa [prefixWord, tailWord_2391972, baseEnd_2391972] using wordTrace_append hprefix tailTrace_2391972
  have hstable : (prefixWord ++ tailWord_2391972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391972).length < 2 ^ (prefixWord ++ tailWord_2391972).sum := by decide
  have hdescent : baseEnd_2391972 < baseStart_2391972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391989 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_2391989 : Nat := 118140960795 + 2391989 * 2 ^ 59
def prefixEnd_2391989 : Nat := 4983230072969 + 3 ^ 40 * 2391989 * 2
def baseEnd_2391989 : Nat := 1228240077267547065736949

theorem tailTrace_2391989 : CollatzResearch.WordTrace tailWord_2391989 prefixEnd_2391989 1228240077267547065736949 := by
  unfold tailWord_2391989
  simp only [CollatzResearch.WordTrace]
  refine ⟨87243006131239847042435021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58162004087493231361623347 87243006131239847042435021)
  ·
    refine ⟨32716127299214942640913133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87243006131239847042435021 32716127299214942640913133)
    ·
      refine ⟨12268547737205603490342425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32716127299214942640913133 12268547737205603490342425)
      ·
        refine ⟨9201410802904202617756819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12268547737205603490342425 9201410802904202617756819)
        ·
          refine ⟨13802116204356303926635229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9201410802904202617756819 13802116204356303926635229)
          ·
            refine ⟨5175793576633613972488211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13802116204356303926635229 5175793576633613972488211)
            ·
              refine ⟨7763690364950420958732317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5175793576633613972488211 7763690364950420958732317)
              ·
                refine ⟨2911383886856407859524619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7763690364950420958732317 2911383886856407859524619)
                ·
                  refine ⟨4367075830284611789286929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911383886856407859524619 4367075830284611789286929)
                  ·
                    refine ⟨3275306872713458841965197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4367075830284611789286929 3275306872713458841965197)
                    ·
                      refine ⟨1228240077267547065736949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3275306872713458841965197 1228240077267547065736949)
                      ·
                        rfl

theorem cell23_2391989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_2391989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2391989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2391989 prefixEnd_2391989 := by exact prefixLift 2391989
  have htrace : WordTrace (prefixWord ++ tailWord_2391989) baseStart_2391989 baseEnd_2391989 := by
    simpa [prefixWord, tailWord_2391989, baseEnd_2391989] using wordTrace_append hprefix tailTrace_2391989
  have hstable : (prefixWord ++ tailWord_2391989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391989).length < 2 ^ (prefixWord ++ tailWord_2391989).sum := by decide
  have hdescent : baseEnd_2391989 < baseStart_2391989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392046 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_2392046 : Nat := 118140960795 + 2392046 * 2 ^ 59
def prefixEnd_2392046 : Nat := 4983230072969 + 3 ^ 40 * 2392046 * 2
def baseEnd_2392046 : Nat := 1228269345664853342724187

theorem tailTrace_2392046 : CollatzResearch.WordTrace tailWord_2392046 prefixEnd_2392046 1228269345664853342724187 := by
  unfold tailWord_2392046
  simp only [CollatzResearch.WordTrace]
  refine ⟨10905635636504168222157499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58163390061355563851506661 10905635636504168222157499)
  ·
    refine ⟨16358453454756252333236249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10905635636504168222157499 16358453454756252333236249)
    ·
      refine ⟨12268840091067189249927187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16358453454756252333236249 12268840091067189249927187)
      ·
        refine ⟨18403260136600783874890781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12268840091067189249927187 18403260136600783874890781)
        ·
          refine ⟨6901222551225293953084043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18403260136600783874890781 6901222551225293953084043)
          ·
            refine ⟨10351833826837940929626065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6901222551225293953084043 10351833826837940929626065)
            ·
              refine ⟨7763875370128455697219549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10351833826837940929626065 7763875370128455697219549)
              ·
                refine ⟨2911453263798170886457331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7763875370128455697219549 2911453263798170886457331)
                ·
                  refine ⟨4367179895697256329685997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911453263798170886457331 4367179895697256329685997)
                  ·
                    refine ⟨1637692460886471123632249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4367179895697256329685997 1637692460886471123632249)
                    ·
                      refine ⟨1228269345664853342724187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1637692460886471123632249 1228269345664853342724187)
                      ·
                        rfl

theorem cell23_2392046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_2392046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392046 prefixEnd_2392046 := by exact prefixLift 2392046
  have htrace : WordTrace (prefixWord ++ tailWord_2392046) baseStart_2392046 baseEnd_2392046 := by
    simpa [prefixWord, tailWord_2392046, baseEnd_2392046] using wordTrace_append hprefix tailTrace_2392046
  have hstable : (prefixWord ++ tailWord_2392046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392046).length < 2 ^ (prefixWord ++ tailWord_2392046).sum := by decide
  have hdescent : baseEnd_2392046 < baseStart_2392046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392059 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 4, 2, 2]
def baseStart_2392059 : Nat := 118140960795 + 2392059 * 2 ^ 59
def prefixEnd_2392059 : Nat := 4983230072969 + 3 ^ 40 * 2392059 * 2
def baseEnd_2392059 : Nat := 1228276020913361791861627

theorem tailTrace_2392059 : CollatzResearch.WordTrace tailWord_2392059 prefixEnd_2392059 1228276020913361791861627 := by
  unfold tailWord_2392059
  simp only [CollatzResearch.WordTrace]
  refine ⟨87245559240986248997483231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58163706160657499331655487 87245559240986248997483231)
  ·
    refine ⟨130868338861479373496224847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87245559240986248997483231 130868338861479373496224847)
    ·
      refine ⟨196302508292219060244337271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130868338861479373496224847 196302508292219060244337271)
      ·
        refine ⟨294453762438328590366505907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196302508292219060244337271 294453762438328590366505907)
        ·
          refine ⟨441680643657492885549758861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294453762438328590366505907 441680643657492885549758861)
          ·
            refine ⟨165630241371559832081159573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 441680643657492885549758861 165630241371559832081159573)
            ·
              refine ⟨7763917564291867128804355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 165630241371559832081159573 7763917564291867128804355)
              ·
                refine ⟨11645876346437800693206533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7763917564291867128804355 11645876346437800693206533)
                ·
                  refine ⟨2183601814957087629976225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11645876346437800693206533 2183601814957087629976225)
                  ·
                    refine ⟨1637701361217815722482169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2183601814957087629976225 1637701361217815722482169)
                    ·
                      refine ⟨1228276020913361791861627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1637701361217815722482169 1228276020913361791861627)
                      ·
                        rfl

theorem cell23_2392059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 2, 2].length) (baseStart_2392059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392059 prefixEnd_2392059 := by exact prefixLift 2392059
  have htrace : WordTrace (prefixWord ++ tailWord_2392059) baseStart_2392059 baseEnd_2392059 := by
    simpa [prefixWord, tailWord_2392059, baseEnd_2392059] using wordTrace_append hprefix tailTrace_2392059
  have hstable : (prefixWord ++ tailWord_2392059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392059).length < 2 ^ (prefixWord ++ tailWord_2392059).sum := by decide
  have hdescent : baseEnd_2392059 < baseStart_2392059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392076 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 2, 2, 2]
def baseStart_2392076 : Nat := 118140960795 + 2392076 * 2 ^ 59
def prefixEnd_2392076 : Nat := 4983230072969 + 3 ^ 40 * 2392076 * 2
def baseEnd_2392076 : Nat := 1228284750084488225349049

theorem tailTrace_2392076 : CollatzResearch.WordTrace tailWord_2392076 prefixEnd_2392076 1228284750084488225349049 := by
  unfold tailWord_2392076
  simp only [CollatzResearch.WordTrace]
  refine ⟨43623089640962330450426041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58164119521283107267234721 43623089640962330450426041)
  ·
    refine ⟨32717317230721747837819531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43623089640962330450426041 32717317230721747837819531)
    ·
      refine ⟨49075975846082621756729297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32717317230721747837819531 49075975846082621756729297)
      ·
        refine ⟨36806981884561966317546973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49075975846082621756729297 36806981884561966317546973)
        ·
          refine ⟨13802618206710737369080115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36806981884561966317546973 13802618206710737369080115)
          ·
            refine ⟨20703927310066106053620173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13802618206710737369080115 20703927310066106053620173)
            ·
              refine ⟨7763972741274789770107565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20703927310066106053620173 7763972741274789770107565)
              ·
                refine ⟨2911489777978046163790337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7763972741274789770107565 2911489777978046163790337)
                ·
                  refine ⟨2183617333483534622842753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2911489777978046163790337 2183617333483534622842753)
                  ·
                    refine ⟨1637713000112650967132065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2183617333483534622842753 1637713000112650967132065)
                    ·
                      refine ⟨1228284750084488225349049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1637713000112650967132065 1228284750084488225349049)
                      ·
                        rfl

theorem cell23_2392076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_2392076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392076 prefixEnd_2392076 := by exact prefixLift 2392076
  have htrace : WordTrace (prefixWord ++ tailWord_2392076) baseStart_2392076 baseEnd_2392076 := by
    simpa [prefixWord, tailWord_2392076, baseEnd_2392076] using wordTrace_append hprefix tailTrace_2392076
  have hstable : (prefixWord ++ tailWord_2392076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392076).length < 2 ^ (prefixWord ++ tailWord_2392076).sum := by decide
  have hdescent : baseEnd_2392076 < baseStart_2392076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392112 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 2, 5]
def baseStart_2392112 : Nat := 118140960795 + 2392112 * 2 ^ 59
def prefixEnd_2392112 : Nat := 4983230072969 + 3 ^ 40 * 2392112 * 2
def baseEnd_2392112 : Nat := 409434411796016694832961

theorem tailTrace_2392112 : CollatzResearch.WordTrace tailWord_2392112 prefixEnd_2392112 409434411796016694832961 := by
  unfold tailWord_2392112
  simp only [CollatzResearch.WordTrace]
  refine ⟨43623746154897119524581295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58164994873196159366108393 43623746154897119524581295)
  ·
    refine ⟨65435619232345679286871943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43623746154897119524581295 65435619232345679286871943)
    ·
      refine ⟨98153428848518518930307915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65435619232345679286871943 98153428848518518930307915)
      ·
        refine ⟨147230143272777778395461873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98153428848518518930307915 147230143272777778395461873)
        ·
          refine ⟨110422607454583333796596405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147230143272777778395461873 110422607454583333796596405)
          ·
            refine ⟨10352119448867187543430913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110422607454583333796596405 10352119448867187543430913)
            ·
              refine ⟨7764089586650390657573185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10352119448867187543430913 7764089586650390657573185)
              ·
                refine ⟨5823067189987792993179889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7764089586650390657573185 5823067189987792993179889)
                ·
                  refine ⟨4367300392490844744884917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5823067189987792993179889 4367300392490844744884917)
                  ·
                    refine ⟨409434411796016694832961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4367300392490844744884917 409434411796016694832961)
                    ·
                      rfl

theorem cell23_2392112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_2392112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392112 prefixEnd_2392112 := by exact prefixLift 2392112
  have htrace : WordTrace (prefixWord ++ tailWord_2392112) baseStart_2392112 baseEnd_2392112 := by
    simpa [prefixWord, tailWord_2392112, baseEnd_2392112] using wordTrace_append hprefix tailTrace_2392112
  have hstable : (prefixWord ++ tailWord_2392112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392112).length < 2 ^ (prefixWord ++ tailWord_2392112).sum := by decide
  have hdescent : baseEnd_2392112 < baseStart_2392112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392126 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2392126 : Nat := 118140960795 + 2392126 * 2 ^ 59
def prefixEnd_2392126 : Nat := 4983230072969 + 3 ^ 40 * 2392126 * 2
def baseEnd_2392126 : Nat := 1228310424117213029723819

theorem tailTrace_2392126 : CollatzResearch.WordTrace tailWord_2392126 prefixEnd_2392126 1228310424117213029723819 := by
  unfold tailWord_2392126
  simp only [CollatzResearch.WordTrace]
  refine ⟨10906000366467939930021529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58165335287829012960114821 10906000366467939930021529)
  ·
    refine ⟨8179500274850954947516147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10906000366467939930021529 8179500274850954947516147)
    ·
      refine ⟨12269250412276432421274221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8179500274850954947516147 12269250412276432421274221)
      ·
        refine ⟨4600968904603662157977833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12269250412276432421274221 4600968904603662157977833)
        ·
          refine ⟨3450726678452746618483375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4600968904603662157977833 3450726678452746618483375)
          ·
            refine ⟨5176090017679119927725063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3450726678452746618483375 5176090017679119927725063)
            ·
              refine ⟨7764135026518679891587595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5176090017679119927725063 7764135026518679891587595)
              ·
                refine ⟨11646202539778019837381393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7764135026518679891587595 11646202539778019837381393)
                ·
                  refine ⟨8734651904833514878036045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11646202539778019837381393 8734651904833514878036045)
                  ·
                    refine ⟨3275494464312568079263517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8734651904833514878036045 3275494464312568079263517)
                    ·
                      refine ⟨1228310424117213029723819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3275494464312568079263517 1228310424117213029723819)
                      ·
                        rfl

theorem cell23_2392126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2392126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392126 prefixEnd_2392126 := by exact prefixLift 2392126
  have htrace : WordTrace (prefixWord ++ tailWord_2392126) baseStart_2392126 baseEnd_2392126 := by
    simpa [prefixWord, tailWord_2392126, baseEnd_2392126] using wordTrace_append hprefix tailTrace_2392126
  have hstable : (prefixWord ++ tailWord_2392126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392126).length < 2 ^ (prefixWord ++ tailWord_2392126).sum := by decide
  have hdescent : baseEnd_2392126 < baseStart_2392126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392146 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_2392146 : Nat := 118140960795 + 2392146 * 2 ^ 59
def prefixEnd_2392146 : Nat := 4983230072969 + 3 ^ 40 * 2392146 * 2
def baseEnd_2392146 : Nat := 409440231243434317157909

theorem tailTrace_2392146 : CollatzResearch.WordTrace tailWord_2392146 prefixEnd_2392146 409440231243434317157909 := by
  unfold tailWord_2392146
  simp only [CollatzResearch.WordTrace]
  refine ⟨21812183097917765713975073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58165821594447375237266861 21812183097917765713975073)
  ·
    refine ⟨16359137323438324285481305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21812183097917765713975073 16359137323438324285481305)
    ·
      refine ⟨12269352992578743214110979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16359137323438324285481305 12269352992578743214110979)
      ·
        refine ⟨18404029488868114821166469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12269352992578743214110979 18404029488868114821166469)
        ·
          refine ⟨3450755529162771528968713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18404029488868114821166469 3450755529162771528968713)
          ·
            refine ⟨2588066646872078646726535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3450755529162771528968713 2588066646872078646726535)
            ·
              refine ⟨3882099970308117970089803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2588066646872078646726535 3882099970308117970089803)
              ·
                refine ⟨5823149955462176955134705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882099970308117970089803 5823149955462176955134705)
                ·
                  refine ⟨4367362466596632716351029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5823149955462176955134705 4367362466596632716351029)
                  ·
                    refine ⟨409440231243434317157909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4367362466596632716351029 409440231243434317157909)
                    ·
                      rfl

theorem cell23_2392146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_2392146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392146 prefixEnd_2392146 := by exact prefixLift 2392146
  have htrace : WordTrace (prefixWord ++ tailWord_2392146) baseStart_2392146 baseEnd_2392146 := by
    simpa [prefixWord, tailWord_2392146, baseEnd_2392146] using wordTrace_append hprefix tailTrace_2392146
  have hstable : (prefixWord ++ tailWord_2392146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392146).length < 2 ^ (prefixWord ++ tailWord_2392146).sum := by decide
  have hdescent : baseEnd_2392146 < baseStart_2392146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392149 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_2392149 : Nat := 118140960795 + 2392149 * 2 ^ 59
def prefixEnd_2392149 : Nat := 4983230072969 + 3 ^ 40 * 2392149 * 2
def baseEnd_2392149 : Nat := 1228322234172266439736213

theorem tailTrace_2392149 : CollatzResearch.WordTrace tailWord_2392149 prefixEnd_2392149 1228322234172266439736213 := by
  unfold tailWord_2392149
  simp only [CollatzResearch.WordTrace]
  refine ⟨87248841810660194368259501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58165894540440129578839667 87248841810660194368259501)
  ·
    refine ⟨32718315678997572888097313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87248841810660194368259501 32718315678997572888097313)
    ·
      refine ⟨24538736759248179666072985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32718315678997572888097313 24538736759248179666072985)
      ·
        refine ⟨18404052569436134749554739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24538736759248179666072985 18404052569436134749554739)
        ·
          refine ⟨27606078854154202124332109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18404052569436134749554739 27606078854154202124332109)
          ·
            refine ⟨10352279570307825796624541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27606078854154202124332109 10352279570307825796624541)
            ·
              refine ⟨3882104838865434673734203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10352279570307825796624541 3882104838865434673734203)
              ·
                refine ⟨5823157258298152010601305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882104838865434673734203 5823157258298152010601305)
                ·
                  refine ⟨4367367943723614007950979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5823157258298152010601305 4367367943723614007950979)
                  ·
                    refine ⟨6551051915585421011926469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4367367943723614007950979 6551051915585421011926469)
                    ·
                      refine ⟨1228322234172266439736213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6551051915585421011926469 1228322234172266439736213)
                      ·
                        rfl

theorem cell23_2392149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_2392149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392149 prefixEnd_2392149 := by exact prefixLift 2392149
  have htrace : WordTrace (prefixWord ++ tailWord_2392149) baseStart_2392149 baseEnd_2392149 := by
    simpa [prefixWord, tailWord_2392149, baseEnd_2392149] using wordTrace_append hprefix tailTrace_2392149
  have hstable : (prefixWord ++ tailWord_2392149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392149).length < 2 ^ (prefixWord ++ tailWord_2392149).sum := by decide
  have hdescent : baseEnd_2392149 < baseStart_2392149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392172 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 8]
def baseStart_2392172 : Nat := 118140960795 + 2392172 * 2 ^ 59
def prefixEnd_2392172 : Nat := 4983230072969 + 3 ^ 40 * 2392172 * 2
def baseEnd_2392172 : Nat := 136481560469702205527623

theorem tailTrace_2392172 : CollatzResearch.WordTrace tailWord_2392172 prefixEnd_2392172 136481560469702205527623 := by
  unfold tailWord_2392172
  simp only [CollatzResearch.WordTrace]
  refine ⟨43624840344788434648173385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58166453793051246197564513 43624840344788434648173385)
  ·
    refine ⟨32718630258591325986130039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43624840344788434648173385 32718630258591325986130039)
    ·
      refine ⟨49077945387886988979195059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32718630258591325986130039 49077945387886988979195059)
      ·
        refine ⟨73616918081830483468792589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49077945387886988979195059 73616918081830483468792589)
        ·
          refine ⟨27606344280686431300797221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73616918081830483468792589 27606344280686431300797221)
          ·
            refine ⟨5176189552628705868899479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27606344280686431300797221 5176189552628705868899479)
            ·
              refine ⟨7764284328943058803349219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5176189552628705868899479 7764284328943058803349219)
              ·
                refine ⟨11646426493414588205023829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7764284328943058803349219 11646426493414588205023829)
                ·
                  refine ⟨136481560469702205527623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11646426493414588205023829 136481560469702205527623)
                  ·
                    rfl

theorem cell23_2392172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_2392172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392172 prefixEnd_2392172 := by exact prefixLift 2392172
  have htrace : WordTrace (prefixWord ++ tailWord_2392172) baseStart_2392172 baseEnd_2392172 := by
    simpa [prefixWord, tailWord_2392172, baseEnd_2392172] using wordTrace_append hprefix tailTrace_2392172
  have hstable : (prefixWord ++ tailWord_2392172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392172).length < 2 ^ (prefixWord ++ tailWord_2392172).sum := by decide
  have hdescent : baseEnd_2392172 < baseStart_2392172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392176 : List Nat := [2, 1, 1, 1, 5, 2, 2, 4, 1, 4]
def baseStart_2392176 : Nat := 118140960795 + 2392176 * 2 ^ 59
def prefixEnd_2392176 : Nat := 4983230072969 + 3 ^ 40 * 2392176 * 2
def baseEnd_2392176 : Nat := 409445366049979278032863

theorem tailTrace_2392176 : CollatzResearch.WordTrace tailWord_2392176 prefixEnd_2392176 409445366049979278032863 := by
  unfold tailWord_2392176
  simp only [CollatzResearch.WordTrace]
  refine ⟨43624913290781188989746191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58166551054374918652994921 43624913290781188989746191)
  ·
    refine ⟨65437369936171783484619287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43624913290781188989746191 65437369936171783484619287)
    ·
      refine ⟨98156054904257675226928931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65437369936171783484619287 98156054904257675226928931)
      ·
        refine ⟨147234082356386512840393397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98156054904257675226928931 147234082356386512840393397)
        ·
          refine ⟨13803195220911235578786881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147234082356386512840393397 13803195220911235578786881)
          ·
            refine ⟨10352396415683426684090161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13803195220911235578786881 10352396415683426684090161)
            ·
              refine ⟨7764297311762570013067621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10352396415683426684090161 7764297311762570013067621)
              ·
                refine ⟨1455805745955481877450179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7764297311762570013067621 1455805745955481877450179)
                ·
                  refine ⟨2183708618933222816175269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455805745955481877450179 2183708618933222816175269)
                  ·
                    refine ⟨409445366049979278032863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2183708618933222816175269 409445366049979278032863)
                    ·
                      rfl

theorem cell23_2392176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 1, 4].length) (baseStart_2392176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392176 prefixEnd_2392176 := by exact prefixLift 2392176
  have htrace : WordTrace (prefixWord ++ tailWord_2392176) baseStart_2392176 baseEnd_2392176 := by
    simpa [prefixWord, tailWord_2392176, baseEnd_2392176] using wordTrace_append hprefix tailTrace_2392176
  have hstable : (prefixWord ++ tailWord_2392176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392176).length < 2 ^ (prefixWord ++ tailWord_2392176).sum := by decide
  have hdescent : baseEnd_2392176 < baseStart_2392176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392209 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 8, 3, 2]
def baseStart_2392209 : Nat := 118140960795 + 2392209 * 2 ^ 59
def prefixEnd_2392209 : Nat := 4983230072969 + 3 ^ 40 * 2392209 * 2
def baseEnd_2392209 : Nat := 1228353043011536204985937

theorem tailTrace_2392209 : CollatzResearch.WordTrace tailWord_2392209 prefixEnd_2392209 1228353043011536204985937 := by
  unfold tailWord_2392209
  simp only [CollatzResearch.WordTrace]
  refine ⟨87251030190442824615443681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58167353460295216410295787 87251030190442824615443681)
  ·
    refine ⟨65438272642832118461582761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87251030190442824615443681 65438272642832118461582761)
    ·
      refine ⟨49078704482124088846187071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65438272642832118461582761 49078704482124088846187071)
      ·
        refine ⟨73618056723186133269280607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49078704482124088846187071 73618056723186133269280607)
        ·
          refine ⟨110427085084779199903920911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73618056723186133269280607 110427085084779199903920911)
          ·
            refine ⟨165640627627168799855881367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110427085084779199903920911 165640627627168799855881367)
            ·
              refine ⟨248460941440753199783822051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165640627627168799855881367 248460941440753199783822051)
              ·
                refine ⟨372691412161129799675733077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248460941440753199783822051 372691412161129799675733077)
                ·
                  refine ⟨4367477486263239839949997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 372691412161129799675733077 4367477486263239839949997)
                  ·
                    refine ⟨1637804057348714939981249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4367477486263239839949997 1637804057348714939981249)
                    ·
                      refine ⟨1228353043011536204985937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1637804057348714939981249 1228353043011536204985937)
                      ·
                        rfl

theorem cell23_2392209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 3, 2].length) (baseStart_2392209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392209 prefixEnd_2392209 := by exact prefixLift 2392209
  have htrace : WordTrace (prefixWord ++ tailWord_2392209) baseStart_2392209 baseEnd_2392209 := by
    simpa [prefixWord, tailWord_2392209, baseEnd_2392209] using wordTrace_append hprefix tailTrace_2392209
  have hstable : (prefixWord ++ tailWord_2392209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392209).length < 2 ^ (prefixWord ++ tailWord_2392209).sum := by decide
  have hdescent : baseEnd_2392209 < baseStart_2392209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392256 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 4]
def baseStart_2392256 : Nat := 118140960795 + 2392256 * 2 ^ 59
def prefixEnd_2392256 : Nat := 4983230072969 + 3 ^ 40 * 2392256 * 2
def baseEnd_2392256 : Nat := 1228377176602297521098221

theorem tailTrace_2392256 : CollatzResearch.WordTrace tailWord_2392256 prefixEnd_2392256 1228377176602297521098221 := by
  unfold tailWord_2392256
  simp only [CollatzResearch.WordTrace]
  refine ⟨43626372210636275821202311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58168496280848367761603081 43626372210636275821202311)
  ·
    refine ⟨65439558315954413731803467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43626372210636275821202311 65439558315954413731803467)
    ·
      refine ⟨98159337473931620597705201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65439558315954413731803467 98159337473931620597705201)
      ·
        refine ⟨73619503105448715448278901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98159337473931620597705201 73619503105448715448278901)
        ·
          refine ⟨6901828416135817073276147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73619503105448715448278901 6901828416135817073276147)
          ·
            refine ⟨10352742624203725609914221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6901828416135817073276147 10352742624203725609914221)
            ·
              refine ⟨3882278484076397103717833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10352742624203725609914221 3882278484076397103717833)
              ·
                refine ⟨2911708863057297827788375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3882278484076397103717833 2911708863057297827788375)
                ·
                  refine ⟨4367563294585946741682563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911708863057297827788375 4367563294585946741682563)
                  ·
                    refine ⟨6551344941878920112523845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4367563294585946741682563 6551344941878920112523845)
                    ·
                      refine ⟨1228377176602297521098221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6551344941878920112523845 1228377176602297521098221)
                      ·
                        rfl

theorem cell23_2392256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_2392256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392256 prefixEnd_2392256 := by exact prefixLift 2392256
  have htrace : WordTrace (prefixWord ++ tailWord_2392256) baseStart_2392256 baseEnd_2392256 := by
    simpa [prefixWord, tailWord_2392256, baseEnd_2392256] using wordTrace_append hprefix tailTrace_2392256
  have hstable : (prefixWord ++ tailWord_2392256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392256).length < 2 ^ (prefixWord ++ tailWord_2392256).sum := by decide
  have hdescent : baseEnd_2392256 < baseStart_2392256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392289 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_2392289 : Nat := 118140960795 + 2392289 * 2 ^ 59
def prefixEnd_2392289 : Nat := 4983230072969 + 3 ^ 40 * 2392289 * 2
def baseEnd_2392289 : Nat := 1228394121463895891985569

theorem tailTrace_2392289 : CollatzResearch.WordTrace tailWord_2392289 prefixEnd_2392289 1228394121463895891985569 := by
  unfold tailWord_2392289
  simp only [CollatzResearch.WordTrace]
  refine ⟨87253948030152998278355921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58169298686768665518903947 87253948030152998278355921)
  ·
    refine ⟨65440461022614748708766941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87253948030152998278355921 65440461022614748708766941)
    ·
      refine ⟨24540172883480530765787603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65440461022614748708766941 24540172883480530765787603)
      ·
        refine ⟨36810259325220796148681405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24540172883480530765787603 36810259325220796148681405)
        ·
          refine ⟨13803847246957798555755527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36810259325220796148681405 13803847246957798555755527)
          ·
            refine ⟨20705770870436697833633291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13803847246957798555755527 20705770870436697833633291)
            ·
              refine ⟨31058656305655046750449937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20705770870436697833633291 31058656305655046750449937)
              ·
                refine ⟨23293992229241285062837453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31058656305655046750449937 23293992229241285062837453)
                ·
                  refine ⟨8735247085965481898564045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23293992229241285062837453 8735247085965481898564045)
                  ·
                    refine ⟨3275717657237055711961517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8735247085965481898564045 3275717657237055711961517)
                    ·
                      refine ⟨1228394121463895891985569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3275717657237055711961517 1228394121463895891985569)
                      ·
                        rfl

theorem cell23_2392289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_2392289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392289 prefixEnd_2392289 := by exact prefixLift 2392289
  have htrace : WordTrace (prefixWord ++ tailWord_2392289) baseStart_2392289 baseEnd_2392289 := by
    simpa [prefixWord, tailWord_2392289, baseEnd_2392289] using wordTrace_append hprefix tailTrace_2392289
  have hstable : (prefixWord ++ tailWord_2392289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392289).length < 2 ^ (prefixWord ++ tailWord_2392289).sum := by decide
  have hdescent : baseEnd_2392289 < baseStart_2392289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392306 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2392306 : Nat := 118140960795 + 2392306 * 2 ^ 59
def prefixEnd_2392306 : Nat := 4983230072969 + 3 ^ 40 * 2392306 * 2
def baseEnd_2392306 : Nat := 1228402850635022325472991

theorem tailTrace_2392306 : CollatzResearch.WordTrace tailWord_2392306 prefixEnd_2392306 1228402850635022325472991 := by
  unfold tailWord_2392306
  simp only [CollatzResearch.WordTrace]
  refine ⟨21813642017772852545431193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58169712047394273454483181 21813642017772852545431193)
  ·
    refine ⟨16360231513329639409073395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21813642017772852545431193 16360231513329639409073395)
    ·
      refine ⟨24540347269994459113610093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16360231513329639409073395 24540347269994459113610093)
      ·
        refine ⟨9202630226247922167603785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24540347269994459113610093 9202630226247922167603785)
        ·
          refine ⟨6901972669685941625702839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9202630226247922167603785 6901972669685941625702839)
          ·
            refine ⟨10352959004528912438554259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6901972669685941625702839 10352959004528912438554259)
            ·
              refine ⟨15529438506793368657831389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10352959004528912438554259 15529438506793368657831389)
              ·
                refine ⟨5823539440047513246686771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15529438506793368657831389 5823539440047513246686771)
                ·
                  refine ⟨8735309160071269870030157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5823539440047513246686771 8735309160071269870030157)
                  ·
                    refine ⟨3275740935026726201261309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8735309160071269870030157 3275740935026726201261309)
                    ·
                      refine ⟨1228402850635022325472991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3275740935026726201261309 1228402850635022325472991)
                      ·
                        rfl

theorem cell23_2392306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2392306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392306 prefixEnd_2392306 := by exact prefixLift 2392306
  have htrace : WordTrace (prefixWord ++ tailWord_2392306) baseStart_2392306 baseEnd_2392306 := by
    simpa [prefixWord, tailWord_2392306, baseEnd_2392306] using wordTrace_append hprefix tailTrace_2392306
  have hstable : (prefixWord ++ tailWord_2392306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392306).length < 2 ^ (prefixWord ++ tailWord_2392306).sum := by decide
  have hdescent : baseEnd_2392306 < baseStart_2392306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392327 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 1, 2, 3]
def baseStart_2392327 : Nat := 118140960795 + 2392327 * 2 ^ 59
def prefixEnd_2392327 : Nat := 4983230072969 + 3 ^ 40 * 2392327 * 2
def baseEnd_2392327 : Nat := 1228413633728766743310395

theorem tailTrace_2392327 : CollatzResearch.WordTrace tailWord_2392327 prefixEnd_2392327 1228413633728766743310395 := by
  unfold tailWord_2392327
  simp only [CollatzResearch.WordTrace]
  refine ⟨87255334004015330768239235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58170222669343553845492823 87255334004015330768239235)
  ·
    refine ⟨130883001006022996152358853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87255334004015330768239235 130883001006022996152358853)
    ·
      refine ⟨24540562688629311778567285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130883001006022996152358853 24540562688629311778567285)
      ·
        refine ⟨2300677752058997979240683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24540562688629311778567285 2300677752058997979240683)
        ·
          refine ⟨3451016628088496968861025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2300677752058997979240683 3451016628088496968861025)
          ·
            refine ⟨2588262471066372726645769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3451016628088496968861025 2588262471066372726645769)
            ·
              refine ⟨1941196853299779544984327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2588262471066372726645769 1941196853299779544984327)
              ·
                refine ⟨2911795279949669317476491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941196853299779544984327 2911795279949669317476491)
                ·
                  refine ⟨4367692919924503976214737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911795279949669317476491 4367692919924503976214737)
                  ·
                    refine ⟨3275769689943377982161053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4367692919924503976214737 3275769689943377982161053)
                    ·
                      refine ⟨1228413633728766743310395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3275769689943377982161053 1228413633728766743310395)
                      ·
                        rfl

theorem cell23_2392327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_2392327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392327 prefixEnd_2392327 := by exact prefixLift 2392327
  have htrace : WordTrace (prefixWord ++ tailWord_2392327) baseStart_2392327 baseEnd_2392327 := by
    simpa [prefixWord, tailWord_2392327, baseEnd_2392327] using wordTrace_append hprefix tailTrace_2392327
  have hstable : (prefixWord ++ tailWord_2392327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392327).length < 2 ^ (prefixWord ++ tailWord_2392327).sum := by decide
  have hdescent : baseEnd_2392327 < baseStart_2392327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392499 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 5]
def baseStart_2392499 : Nat := 118140960795 + 2392499 * 2 ^ 59
def prefixEnd_2392499 : Nat := 4983230072969 + 3 ^ 40 * 2392499 * 2
def baseEnd_2392499 : Nat := 1228501952401340070359603

theorem tailTrace_2392499 : CollatzResearch.WordTrace tailWord_2392499 prefixEnd_2392499 1228501952401340070359603 := by
  unfold tailWord_2392499
  simp only [CollatzResearch.WordTrace]
  refine ⟨87261607359392204143500551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58174404906261469429000367 87261607359392204143500551)
  ·
    refine ⟨130892411039088306215250827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87261607359392204143500551 130892411039088306215250827)
    ·
      refine ⟨196338616558632459322876241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130892411039088306215250827 196338616558632459322876241)
      ·
        refine ⟨147253962418974344492157181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196338616558632459322876241 147253962418974344492157181)
        ·
          refine ⟨55220235907115379184558943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147253962418974344492157181 55220235907115379184558943)
          ·
            refine ⟨82830353860673068776838415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55220235907115379184558943 82830353860673068776838415)
            ·
              refine ⟨124245530791009603165257623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82830353860673068776838415 124245530791009603165257623)
              ·
                refine ⟨186368296186514404747886435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124245530791009603165257623 186368296186514404747886435)
                ·
                  refine ⟨279552444279771607121829653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186368296186514404747886435 279552444279771607121829653)
                  ·
                    refine ⟨13104020825614294083835765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 279552444279771607121829653 13104020825614294083835765)
                    ·
                      refine ⟨1228501952401340070359603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13104020825614294083835765 1228501952401340070359603)
                      ·
                        rfl

theorem cell23_2392499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_2392499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392499 prefixEnd_2392499 := by exact prefixLift 2392499
  have htrace : WordTrace (prefixWord ++ tailWord_2392499) baseStart_2392499 baseEnd_2392499 := by
    simpa [prefixWord, tailWord_2392499, baseEnd_2392499] using wordTrace_append hprefix tailTrace_2392499
  have hstable : (prefixWord ++ tailWord_2392499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392499).length < 2 ^ (prefixWord ++ tailWord_2392499).sum := by decide
  have hdescent : baseEnd_2392499 < baseStart_2392499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392520 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_2392520 : Nat := 118140960795 + 2392520 * 2 ^ 59
def prefixEnd_2392520 : Nat := 4983230072969 + 3 ^ 40 * 2392520 * 2
def baseEnd_2392520 : Nat := 1228512735495084488197007

theorem tailTrace_2392520 : CollatzResearch.WordTrace tailWord_2392520 prefixEnd_2392520 1228512735495084488197007 := by
  unfold tailWord_2392520
  simp only [CollatzResearch.WordTrace]
  refine ⟨43631186646158062365007507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58174915528210749820010009 43631186646158062365007507)
  ·
    refine ⟨65446779969237093547511261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43631186646158062365007507 65446779969237093547511261)
    ·
      refine ⟨24542542488463910080316723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65446779969237093547511261 24542542488463910080316723)
      ·
        refine ⟨36813813732695865120475085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24542542488463910080316723 36813813732695865120475085)
        ·
          refine ⟨13805180149760949420178157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36813813732695865120475085 13805180149760949420178157)
          ·
            refine ⟨5176942556160356032566809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13805180149760949420178157 5176942556160356032566809)
            ·
              refine ⟨3882706917120267024425107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5176942556160356032566809 3882706917120267024425107)
              ·
                refine ⟨5824060375680400536637661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882706917120267024425107 5824060375680400536637661)
                ·
                  refine ⟨2184022640880150201239123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5824060375680400536637661 2184022640880150201239123)
                  ·
                    refine ⟨3276033961320225301858685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2184022640880150201239123 3276033961320225301858685)
                    ·
                      refine ⟨1228512735495084488197007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3276033961320225301858685 1228512735495084488197007)
                      ·
                        rfl

theorem cell23_2392520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_2392520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392520 prefixEnd_2392520 := by exact prefixLift 2392520
  have htrace : WordTrace (prefixWord ++ tailWord_2392520) baseStart_2392520 baseEnd_2392520 := by
    simpa [prefixWord, tailWord_2392520, baseEnd_2392520] using wordTrace_append hprefix tailTrace_2392520
  have hstable : (prefixWord ++ tailWord_2392520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392520).length < 2 ^ (prefixWord ++ tailWord_2392520).sum := by decide
  have hdescent : baseEnd_2392520 < baseStart_2392520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392543 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 4]
def baseStart_2392543 : Nat := 118140960795 + 2392543 * 2 ^ 59
def prefixEnd_2392543 : Nat := 4983230072969 + 3 ^ 40 * 2392543 * 2
def baseEnd_2392543 : Nat := 1228524545550137898209401

theorem tailTrace_2392543 : CollatzResearch.WordTrace tailWord_2392543 prefixEnd_2392543 1228524545550137898209401 := by
  unfold tailWord_2392543
  simp only [CollatzResearch.WordTrace]
  refine ⟨87263212171232799658102283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58175474780821866438734855 87263212171232799658102283)
  ·
    refine ⟨130894818256849199487153425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87263212171232799658102283 130894818256849199487153425)
    ·
      refine ⟨98171113692636899615365069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130894818256849199487153425 98171113692636899615365069)
      ·
        refine ⟨36814167634738837355761901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98171113692636899615365069 36814167634738837355761901)
        ·
          refine ⟨13805312863027064008410713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36814167634738837355761901 13805312863027064008410713)
          ·
            refine ⟨10353984647270298006308035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13805312863027064008410713 10353984647270298006308035)
            ·
              refine ⟨15530976970905447009462053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10353984647270298006308035 15530976970905447009462053)
              ·
                refine ⟨2912058182044771314274135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15530976970905447009462053 2912058182044771314274135)
                ·
                  refine ⟨4368087273067156971411203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912058182044771314274135 4368087273067156971411203)
                  ·
                    refine ⟨6552130909600735457116805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4368087273067156971411203 6552130909600735457116805)
                    ·
                      refine ⟨1228524545550137898209401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6552130909600735457116805 1228524545550137898209401)
                      ·
                        rfl

theorem cell23_2392543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_2392543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392543 prefixEnd_2392543 := by exact prefixLift 2392543
  have htrace : WordTrace (prefixWord ++ tailWord_2392543) baseStart_2392543 baseEnd_2392543 := by
    simpa [prefixWord, tailWord_2392543, baseEnd_2392543] using wordTrace_append hprefix tailTrace_2392543
  have hstable : (prefixWord ++ tailWord_2392543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392543).length < 2 ^ (prefixWord ++ tailWord_2392543).sum := by decide
  have hdescent : baseEnd_2392543 < baseStart_2392543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392554 : List Nat := [3, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_2392554 : Nat := 118140960795 + 2392554 * 2 ^ 59
def prefixEnd_2392554 : Nat := 4983230072969 + 3 ^ 40 * 2392554 * 2
def baseEnd_2392554 : Nat := 1228530193837337355171851

theorem tailTrace_2392554 : CollatzResearch.WordTrace tailWord_2392554 prefixEnd_2392554 1228530193837337355171851 := by
  unfold tailWord_2392554
  simp only [CollatzResearch.WordTrace]
  refine ⟨21815903343548237134188179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58175742249461965691168477 21815903343548237134188179)
  ·
    refine ⟨32723855015322355701282269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21815903343548237134188179 32723855015322355701282269)
    ·
      refine ⟨12271445630745883387980851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32723855015322355701282269 12271445630745883387980851)
      ·
        refine ⟨18407168446118825081971277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12271445630745883387980851 18407168446118825081971277)
        ·
          refine ⟨6902688167294559405739229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18407168446118825081971277 6902688167294559405739229)
          ·
            refine ⟨2588508062735459777152211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6902688167294559405739229 2588508062735459777152211)
            ·
              refine ⟨3882762094103189665728317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2588508062735459777152211 3882762094103189665728317)
              ·
                refine ⟨1456035785288696124648119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3882762094103189665728317 1456035785288696124648119)
                ·
                  refine ⟨2184053677933044186972179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456035785288696124648119 2184053677933044186972179)
                  ·
                    refine ⟨3276080516899566280458269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2184053677933044186972179 3276080516899566280458269)
                    ·
                      refine ⟨1228530193837337355171851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3276080516899566280458269 1228530193837337355171851)
                      ·
                        rfl

theorem cell23_2392554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_2392554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392554 prefixEnd_2392554 := by exact prefixLift 2392554
  have htrace : WordTrace (prefixWord ++ tailWord_2392554) baseStart_2392554 baseEnd_2392554 := by
    simpa [prefixWord, tailWord_2392554, baseEnd_2392554] using wordTrace_append hprefix tailTrace_2392554
  have hstable : (prefixWord ++ tailWord_2392554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392554).length < 2 ^ (prefixWord ++ tailWord_2392554).sum := by decide
  have hdescent : baseEnd_2392554 < baseStart_2392554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392556 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_2392556 : Nat := 118140960795 + 2392556 * 2 ^ 59
def prefixEnd_2392556 : Nat := 4983230072969 + 3 ^ 40 * 2392556 * 2
def baseEnd_2392556 : Nat := 1228531220798646347346841

theorem tailTrace_2392556 : CollatzResearch.WordTrace tailWord_2392556 prefixEnd_2392556 1228531220798646347346841 := by
  unfold tailWord_2392556
  simp only [CollatzResearch.WordTrace]
  refine ⟨43631843160092851439162761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58175790880123801918883681 43631843160092851439162761)
  ·
    refine ⟨32723882370069638579372071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43631843160092851439162761 32723882370069638579372071)
    ·
      refine ⟨49085823555104457869058107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32723882370069638579372071 49085823555104457869058107)
      ·
        refine ⟨73628735332656686803587161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49085823555104457869058107 73628735332656686803587161)
        ·
          refine ⟨55221551499492515102690371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73628735332656686803587161 55221551499492515102690371)
          ·
            refine ⟨82832327249238772654035557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55221551499492515102690371 82832327249238772654035557)
            ·
              refine ⟨15531061359232269872631667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82832327249238772654035557 15531061359232269872631667)
              ·
                refine ⟨23296592038848404808947501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15531061359232269872631667 23296592038848404808947501)
                ·
                  refine ⟨8736222014568151803355313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23296592038848404808947501 8736222014568151803355313)
                  ·
                    refine ⟨6552166510926113852516485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8736222014568151803355313 6552166510926113852516485)
                    ·
                      refine ⟨1228531220798646347346841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6552166510926113852516485 1228531220798646347346841)
                      ·
                        rfl

theorem cell23_2392556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_2392556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392556 prefixEnd_2392556 := by exact prefixLift 2392556
  have htrace : WordTrace (prefixWord ++ tailWord_2392556) baseStart_2392556 baseEnd_2392556 := by
    simpa [prefixWord, tailWord_2392556, baseEnd_2392556] using wordTrace_append hprefix tailTrace_2392556
  have hstable : (prefixWord ++ tailWord_2392556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392556).length < 2 ^ (prefixWord ++ tailWord_2392556).sum := by decide
  have hdescent : baseEnd_2392556 < baseStart_2392556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392563 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 1, 2, 3]
def baseStart_2392563 : Nat := 118140960795 + 2392563 * 2 ^ 59
def prefixEnd_2392563 : Nat := 4983230072969 + 3 ^ 40 * 2392563 * 2
def baseEnd_2392563 : Nat := 1228534815163227819959309

theorem tailTrace_2392563 : CollatzResearch.WordTrace tailWord_2392563 prefixEnd_2392563 1228534815163227819959309 := by
  unfold tailWord_2392563
  simp only [CollatzResearch.WordTrace]
  refine ⟨87263941631160343073830343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58175961087440228715886895 87263941631160343073830343)
  ·
    refine ⟨130895912446740514610745515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87263941631160343073830343 130895912446740514610745515)
    ·
      refine ⟨196343868670110771916118273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130895912446740514610745515 196343868670110771916118273)
      ·
        refine ⟨147257901502583078937088705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196343868670110771916118273 147257901502583078937088705)
        ·
          refine ⟨110443426126937309202816529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147257901502583078937088705 110443426126937309202816529)
          ·
            refine ⟨82832569595202981902112397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110443426126937309202816529 82832569595202981902112397)
            ·
              refine ⟨31062213598201118213292149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82832569595202981902112397 31062213598201118213292149)
              ·
                refine ⟨2912082524831354832496139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31062213598201118213292149 2912082524831354832496139)
                ·
                  refine ⟨4368123787247032248744209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912082524831354832496139 4368123787247032248744209)
                  ·
                    refine ⟨3276092840435274186558157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4368123787247032248744209 3276092840435274186558157)
                    ·
                      refine ⟨1228534815163227819959309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3276092840435274186558157 1228534815163227819959309)
                      ·
                        rfl

theorem cell23_2392563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 2, 3].length) (baseStart_2392563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392563 prefixEnd_2392563 := by exact prefixLift 2392563
  have htrace : WordTrace (prefixWord ++ tailWord_2392563) baseStart_2392563 baseEnd_2392563 := by
    simpa [prefixWord, tailWord_2392563, baseEnd_2392563] using wordTrace_append hprefix tailTrace_2392563
  have hstable : (prefixWord ++ tailWord_2392563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392563).length < 2 ^ (prefixWord ++ tailWord_2392563).sum := by decide
  have hdescent : baseEnd_2392563 < baseStart_2392563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392577 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_2392577 : Nat := 118140960795 + 2392577 * 2 ^ 59
def prefixEnd_2392577 : Nat := 4983230072969 + 3 ^ 40 * 2392577 * 2
def baseEnd_2392577 : Nat := 1228542003892390765184245

theorem tailTrace_2392577 : CollatzResearch.WordTrace tailWord_2392577 prefixEnd_2392577 1228542003892390765184245 := by
  unfold tailWord_2392577
  simp only [CollatzResearch.WordTrace]
  refine ⟨87264452253109623464839985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58176301502073082309893323 87264452253109623464839985)
  ·
    refine ⟨65448339189832217598629989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87264452253109623464839985 65448339189832217598629989)
    ·
      refine ⟨12271563598093540799743123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65448339189832217598629989 12271563598093540799743123)
      ·
        refine ⟨18407345397140311199614685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12271563598093540799743123 18407345397140311199614685)
        ·
          refine ⟨6902754523927616699855507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18407345397140311199614685 6902754523927616699855507)
          ·
            refine ⟨10354131785891425049783261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6902754523927616699855507 10354131785891425049783261)
            ·
              refine ⟨3882799419709284393668723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10354131785891425049783261 3882799419709284393668723)
              ·
                refine ⟨5824199129563926590503085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882799419709284393668723 5824199129563926590503085)
                ·
                  refine ⟨2184074673586472471438657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5824199129563926590503085 2184074673586472471438657)
                  ·
                    refine ⟨1638056005189854353578993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2184074673586472471438657 1638056005189854353578993)
                    ·
                      refine ⟨1228542003892390765184245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638056005189854353578993 1228542003892390765184245)
                      ·
                        rfl

theorem cell23_2392577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_2392577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392577 prefixEnd_2392577 := by exact prefixLift 2392577
  have htrace : WordTrace (prefixWord ++ tailWord_2392577) baseStart_2392577 baseEnd_2392577 := by
    simpa [prefixWord, tailWord_2392577, baseEnd_2392577] using wordTrace_append hprefix tailTrace_2392577
  have hstable : (prefixWord ++ tailWord_2392577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392577).length < 2 ^ (prefixWord ++ tailWord_2392577).sum := by decide
  have hdescent : baseEnd_2392577 < baseStart_2392577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392583 : List Nat := [1, 1, 4, 3, 3, 1, 2, 8]
def baseStart_2392583 : Nat := 118140960795 + 2392583 * 2 ^ 59
def prefixEnd_2392583 : Nat := 4983230072969 + 3 ^ 40 * 2392583 * 2
def baseEnd_2392583 : Nat := 45501669806530286729971

theorem tailTrace_2392583 : CollatzResearch.WordTrace tailWord_2392583 prefixEnd_2392583 45501669806530286729971 := by
  unfold tailWord_2392583
  simp only [CollatzResearch.WordTrace]
  refine ⟨87264671091087886489558403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58176447394058590993038935 87264671091087886489558403)
  ·
    refine ⟨130897006636631829734337605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87264671091087886489558403 130897006636631829734337605)
    ·
      refine ⟨24543188744368468075188301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130897006636631829734337605 24543188744368468075188301)
      ·
        refine ⟨9203695779138175528195613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24543188744368468075188301 9203695779138175528195613)
        ·
          refine ⟨3451385917176815823073355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9203695779138175528195613 3451385917176815823073355)
          ·
            refine ⟨5177078875765223734610033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3451385917176815823073355 5177078875765223734610033)
            ·
              refine ⟨3882809156823917800957525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5177078875765223734610033 3882809156823917800957525)
              ·
                refine ⟨45501669806530286729971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3882809156823917800957525 45501669806530286729971)
                ·
                  rfl

theorem cell23_2392583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 8].length) (baseStart_2392583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392583 prefixEnd_2392583 := by exact prefixLift 2392583
  have htrace : WordTrace (prefixWord ++ tailWord_2392583) baseStart_2392583 baseEnd_2392583 := by
    simpa [prefixWord, tailWord_2392583, baseEnd_2392583] using wordTrace_append hprefix tailTrace_2392583
  have hstable : (prefixWord ++ tailWord_2392583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392583).length < 2 ^ (prefixWord ++ tailWord_2392583).sum := by decide
  have hdescent : baseEnd_2392583 < baseStart_2392583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392586 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2392586 : Nat := 118140960795 + 2392586 * 2 ^ 59
def prefixEnd_2392586 : Nat := 4983230072969 + 3 ^ 40 * 2392586 * 2
def baseEnd_2392586 : Nat := 1228546625218281229971703

theorem tailTrace_2392586 : CollatzResearch.WordTrace tailWord_2392586 prefixEnd_2392586 1228546625218281229971703 := by
  unfold tailWord_2392586
  simp only [CollatzResearch.WordTrace]
  refine ⟨21816195127519254500479403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58176520340051345334611741 21816195127519254500479403)
  ·
    refine ⟨32724292691278881750719105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21816195127519254500479403 32724292691278881750719105)
    ·
      refine ⟨24543219518459161313039329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32724292691278881750719105 24543219518459161313039329)
      ·
        refine ⟨18407414638844370984779497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24543219518459161313039329 18407414638844370984779497)
        ·
          refine ⟨13805560979133278238584623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18407414638844370984779497 13805560979133278238584623)
          ·
            refine ⟨20708341468699917357876935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13805560979133278238584623 20708341468699917357876935)
            ·
              refine ⟨31062512203049876036815403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20708341468699917357876935 31062512203049876036815403)
              ·
                refine ⟨46593768304574814055223105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31062512203049876036815403 46593768304574814055223105)
                ·
                  refine ⟨34945326228431110541417329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46593768304574814055223105 34945326228431110541417329)
                  ·
                    refine ⟨26208994671323332906062997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34945326228431110541417329 26208994671323332906062997)
                    ·
                      refine ⟨1228546625218281229971703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26208994671323332906062997 1228546625218281229971703)
                      ·
                        rfl

theorem cell23_2392586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2392586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392586 prefixEnd_2392586 := by exact prefixLift 2392586
  have htrace : WordTrace (prefixWord ++ tailWord_2392586) baseStart_2392586 baseEnd_2392586 := by
    simpa [prefixWord, tailWord_2392586, baseEnd_2392586] using wordTrace_append hprefix tailTrace_2392586
  have hstable : (prefixWord ++ tailWord_2392586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392586).length < 2 ^ (prefixWord ++ tailWord_2392586).sum := by decide
  have hdescent : baseEnd_2392586 < baseStart_2392586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392587 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 2, 4]
def baseStart_2392587 : Nat := 118140960795 + 2392587 * 2 ^ 59
def prefixEnd_2392587 : Nat := 4983230072969 + 3 ^ 40 * 2392587 * 2
def baseEnd_2392587 : Nat := 409515712899645242019733

theorem tailTrace_2392587 : CollatzResearch.WordTrace tailWord_2392587 prefixEnd_2392587 409515712899645242019733 := by
  unfold tailWord_2392587
  simp only [CollatzResearch.WordTrace]
  refine ⟨87264816983073395172704015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58176544655382263448469343 87264816983073395172704015)
  ·
    refine ⟨130897225474610092759056023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87264816983073395172704015 130897225474610092759056023)
    ·
      refine ⟨196345838211915139138584035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130897225474610092759056023 196345838211915139138584035)
      ·
        refine ⟨294518757317872708707876053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196345838211915139138584035 294518757317872708707876053)
        ·
          refine ⟨6902783374637641610340845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 294518757317872708707876053 6902783374637641610340845)
          ·
            refine ⟨2588543765489115603877817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6902783374637641610340845 2588543765489115603877817)
            ·
              refine ⟨1941407824116836702908363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2588543765489115603877817 1941407824116836702908363)
              ·
                refine ⟨2912111736175255054362545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941407824116836702908363 2912111736175255054362545)
                ·
                  refine ⟨2184083802131441290771909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2912111736175255054362545 2184083802131441290771909)
                  ·
                    refine ⟨409515712899645242019733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2184083802131441290771909 409515712899645242019733)
                    ·
                      rfl

theorem cell23_2392587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 2, 4].length) (baseStart_2392587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392587 prefixEnd_2392587 := by exact prefixLift 2392587
  have htrace : WordTrace (prefixWord ++ tailWord_2392587) baseStart_2392587 baseEnd_2392587 := by
    simpa [prefixWord, tailWord_2392587, baseEnd_2392587] using wordTrace_append hprefix tailTrace_2392587
  have hstable : (prefixWord ++ tailWord_2392587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392587).length < 2 ^ (prefixWord ++ tailWord_2392587).sum := by decide
  have hdescent : baseEnd_2392587 < baseStart_2392587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392593 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 6, 1, 3]
def baseStart_2392593 : Nat := 118140960795 + 2392593 * 2 ^ 59
def prefixEnd_2392593 : Nat := 4983230072969 + 3 ^ 40 * 2392593 * 2
def baseEnd_2392593 : Nat := 1228550219582862702584171

theorem tailTrace_2392593 : CollatzResearch.WordTrace tailWord_2392593 prefixEnd_2392593 1228550219582862702584171 := by
  unfold tailWord_2392593
  simp only [CollatzResearch.WordTrace]
  refine ⟨87265035821051658197422433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58176690547367772131614955 87265035821051658197422433)
  ·
    refine ⟨65448776865788743648066825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87265035821051658197422433 65448776865788743648066825)
    ·
      refine ⟨49086582649341557736050119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65448776865788743648066825 49086582649341557736050119)
      ·
        refine ⟨73629873974012336604075179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49086582649341557736050119 73629873974012336604075179)
        ·
          refine ⟨110444810961018504906112769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73629873974012336604075179 110444810961018504906112769)
          ·
            refine ⟨82833608220763878679584577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110444810961018504906112769 82833608220763878679584577)
            ·
              refine ⟨62125206165572909009688433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82833608220763878679584577 62125206165572909009688433)
              ·
                refine ⟨46593904624179681757266325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62125206165572909009688433 46593904624179681757266325)
                ·
                  refine ⟨2184089279258422582371859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46593904624179681757266325 2184089279258422582371859)
                  ·
                    refine ⟨3276133918887633873557789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2184089279258422582371859 3276133918887633873557789)
                    ·
                      refine ⟨1228550219582862702584171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3276133918887633873557789 1228550219582862702584171)
                      ·
                        rfl

theorem cell23_2392593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_2392593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392593 prefixEnd_2392593 := by exact prefixLift 2392593
  have htrace : WordTrace (prefixWord ++ tailWord_2392593) baseStart_2392593 baseEnd_2392593 := by
    simpa [prefixWord, tailWord_2392593, baseEnd_2392593] using wordTrace_append hprefix tailTrace_2392593
  have hstable : (prefixWord ++ tailWord_2392593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392593).length < 2 ^ (prefixWord ++ tailWord_2392593).sum := by decide
  have hdescent : baseEnd_2392593 < baseStart_2392593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392620 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 1, 3, 2]
def baseStart_2392620 : Nat := 118140960795 + 2392620 * 2 ^ 59
def prefixEnd_2392620 : Nat := 4983230072969 + 3 ^ 40 * 2392620 * 2
def baseEnd_2392620 : Nat := 1228564083560534096946547

theorem tailTrace_2392620 : CollatzResearch.WordTrace tailWord_2392620 prefixEnd_2392620 1228564083560534096946547 := by
  unfold tailWord_2392620
  simp only [CollatzResearch.WordTrace]
  refine ⟨43633010295976920904327657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58177347061302561205770209 43633010295976920904327657)
  ·
    refine ⟨32724757721982690678245743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43633010295976920904327657 32724757721982690678245743)
    ·
      refine ⟨49087136582974036017368615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32724757721982690678245743 49087136582974036017368615)
      ·
        refine ⟨73630704874461054026052923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49087136582974036017368615 73630704874461054026052923)
        ·
          refine ⟨110446057311691581039079385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73630704874461054026052923 110446057311691581039079385)
          ·
            refine ⟨82834542983768685779309539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110446057311691581039079385 82834542983768685779309539)
            ·
              refine ⟨124251814475653028668964309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82834542983768685779309539 124251814475653028668964309)
              ·
                refine ⟨2912151901773117859428851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 124251814475653028668964309 2912151901773117859428851)
                ·
                  refine ⟨4368227852659676789143277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912151901773117859428851 4368227852659676789143277)
                  ·
                    refine ⟨1638085444747378795928729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4368227852659676789143277 1638085444747378795928729)
                    ·
                      refine ⟨1228564083560534096946547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638085444747378795928729 1228564083560534096946547)
                      ·
                        rfl

theorem cell23_2392620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 3, 2].length) (baseStart_2392620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392620 prefixEnd_2392620 := by exact prefixLift 2392620
  have htrace : WordTrace (prefixWord ++ tailWord_2392620) baseStart_2392620 baseEnd_2392620 := by
    simpa [prefixWord, tailWord_2392620, baseEnd_2392620] using wordTrace_append hprefix tailTrace_2392620
  have hstable : (prefixWord ++ tailWord_2392620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392620).length < 2 ^ (prefixWord ++ tailWord_2392620).sum := by decide
  have hdescent : baseEnd_2392620 < baseStart_2392620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392621 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2392621 : Nat := 118140960795 + 2392621 * 2 ^ 59
def prefixEnd_2392621 : Nat := 4983230072969 + 3 ^ 40 * 2392621 * 2
def baseEnd_2392621 : Nat := 409521532347062864344681

theorem tailTrace_2392621 : CollatzResearch.WordTrace tailWord_2392621 prefixEnd_2392621 409521532347062864344681 := by
  unfold tailWord_2392621
  simp only [CollatzResearch.WordTrace]
  refine ⟨87266057064950218979441717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58177371376633479319627811 87266057064950218979441717)
  ·
    refine ⟨8181192849839083029322661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87266057064950218979441717 8181192849839083029322661)
    ·
      refine ⟨1533973659344828067997999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8181192849839083029322661 1533973659344828067997999)
      ·
        refine ⟨2300960489017242101996999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1533973659344828067997999 2300960489017242101996999)
        ·
          refine ⟨3451440733525863152995499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2300960489017242101996999 3451440733525863152995499)
          ·
            refine ⟨5177161100288794729493249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3451440733525863152995499 5177161100288794729493249)
            ·
              refine ⟨3882870825216596047119937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5177161100288794729493249 3882870825216596047119937)
              ·
                refine ⟨2912153118912447035339953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3882870825216596047119937 2912153118912447035339953)
                ·
                  refine ⟨2184114839184335276504965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2912153118912447035339953 2184114839184335276504965)
                  ·
                    refine ⟨409521532347062864344681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2184114839184335276504965 409521532347062864344681)
                    ·
                      rfl

theorem cell23_2392621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2392621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392621 prefixEnd_2392621 := by exact prefixLift 2392621
  have htrace : WordTrace (prefixWord ++ tailWord_2392621) baseStart_2392621 baseEnd_2392621 := by
    simpa [prefixWord, tailWord_2392621, baseEnd_2392621] using wordTrace_append hprefix tailTrace_2392621
  have hstable : (prefixWord ++ tailWord_2392621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392621).length < 2 ^ (prefixWord ++ tailWord_2392621).sum := by decide
  have hdescent : baseEnd_2392621 < baseStart_2392621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392628 : List Nat := [2, 5, 1, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_2392628 : Nat := 118140960795 + 2392628 * 2 ^ 59
def prefixEnd_2392628 : Nat := 4983230072969 + 3 ^ 40 * 2392628 * 2
def baseEnd_2392628 : Nat := 1228568191405770065646511

theorem tailTrace_2392628 : CollatzResearch.WordTrace tailWord_2392628 prefixEnd_2392628 1228568191405770065646511 := by
  unfold tailWord_2392628
  simp only [CollatzResearch.WordTrace]
  refine ⟨43633156187962429587473269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58177541583949906116631025 43633156187962429587473269)
  ·
    refine ⟨4090608392621477773825619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43633156187962429587473269 4090608392621477773825619)
    ·
      refine ⟨6135912588932216660738429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4090608392621477773825619 6135912588932216660738429)
      ·
        refine ⟨2300967220849581247776911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6135912588932216660738429 2300967220849581247776911)
        ·
          refine ⟨3451450831274371871665367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2300967220849581247776911 3451450831274371871665367)
          ·
            refine ⟨5177176246911557807498051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3451450831274371871665367 5177176246911557807498051)
            ·
              refine ⟨7765764370367336711247077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5177176246911557807498051 7765764370367336711247077)
              ·
                refine ⟨1456080819443875633358827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7765764370367336711247077 1456080819443875633358827)
                ·
                  refine ⟨2184121229165813450038241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456080819443875633358827 2184121229165813450038241)
                  ·
                    refine ⟨1638090921874360087528681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2184121229165813450038241 1638090921874360087528681)
                    ·
                      refine ⟨1228568191405770065646511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638090921874360087528681 1228568191405770065646511)
                      ·
                        rfl

theorem cell23_2392628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_2392628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392628 prefixEnd_2392628 := by exact prefixLift 2392628
  have htrace : WordTrace (prefixWord ++ tailWord_2392628) baseStart_2392628 baseEnd_2392628 := by
    simpa [prefixWord, tailWord_2392628, baseEnd_2392628] using wordTrace_append hprefix tailTrace_2392628
  have hstable : (prefixWord ++ tailWord_2392628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392628).length < 2 ^ (prefixWord ++ tailWord_2392628).sum := by decide
  have hdescent : baseEnd_2392628 < baseStart_2392628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392650 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2]
def baseStart_2392650 : Nat := 118140960795 + 2392650 * 2 ^ 59
def prefixEnd_2392650 : Nat := 4983230072969 + 3 ^ 40 * 2392650 * 2
def baseEnd_2392650 : Nat := 1228579487980168979571409

theorem tailTrace_2392650 : CollatzResearch.WordTrace tailWord_2392650 prefixEnd_2392650 1228579487980168979571409 := by
  unfold tailWord_2392650
  simp only [CollatzResearch.WordTrace]
  refine ⟨21816778695461289233061851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58178076521230104621498269 21816778695461289233061851)
  ·
    refine ⟨32725168043191933849592777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21816778695461289233061851 32725168043191933849592777)
    ·
      refine ⟨24543876032393950387194583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32725168043191933849592777 24543876032393950387194583)
      ·
        refine ⟨36815814048590925580791875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24543876032393950387194583 36815814048590925580791875)
        ·
          refine ⟨55223721072886388371187813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36815814048590925580791875 55223721072886388371187813)
          ·
            refine ⟨10354447701166197819597715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55223721072886388371187813 10354447701166197819597715)
            ·
              refine ⟨15531671551749296729396573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10354447701166197819597715 15531671551749296729396573)
              ·
                refine ⟨5824376831905986273523715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15531671551749296729396573 5824376831905986273523715)
                ·
                  refine ⟨8736565247858979410285573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5824376831905986273523715 8736565247858979410285573)
                  ·
                    refine ⟨1638105983973558639428545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8736565247858979410285573 1638105983973558639428545)
                    ·
                      refine ⟨1228579487980168979571409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638105983973558639428545 1228579487980168979571409)
                      ·
                        rfl

theorem cell23_2392650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_2392650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392650 prefixEnd_2392650 := by exact prefixLift 2392650
  have htrace : WordTrace (prefixWord ++ tailWord_2392650) baseStart_2392650 baseEnd_2392650 := by
    simpa [prefixWord, tailWord_2392650, baseEnd_2392650] using wordTrace_append hprefix tailTrace_2392650
  have hstable : (prefixWord ++ tailWord_2392650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392650).length < 2 ^ (prefixWord ++ tailWord_2392650).sum := by decide
  have hdescent : baseEnd_2392650 < baseStart_2392650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392666 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_2392666 : Nat := 118140960795 + 2392666 * 2 ^ 59
def prefixEnd_2392666 : Nat := 4983230072969 + 3 ^ 40 * 2392666 * 2
def baseEnd_2392666 : Nat := 1228587703670640916971335

theorem tailTrace_2392666 : CollatzResearch.WordTrace tailWord_2392666 prefixEnd_2392666 1228587703670640916971335 := by
  unfold tailWord_2392666
  simp only [CollatzResearch.WordTrace]
  refine ⟨21816924587446797916207463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58178465566524794443219901 21816924587446797916207463)
  ·
    refine ⟨32725386881170196874311195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21816924587446797916207463 32725386881170196874311195)
    ·
      refine ⟨49088080321755295311466793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32725386881170196874311195 49088080321755295311466793)
      ·
        refine ⟨36816060241316471483600095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49088080321755295311466793 36816060241316471483600095)
        ·
          refine ⟨55224090361974707225400143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36816060241316471483600095 55224090361974707225400143)
          ·
            refine ⟨82836135542962060838100215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55224090361974707225400143 82836135542962060838100215)
            ·
              refine ⟨124254203314443091257150323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82836135542962060838100215 124254203314443091257150323)
              ·
                refine ⟨186381304971664636885725485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124254203314443091257150323 186381304971664636885725485)
                ·
                  refine ⟨69892989364374238832147057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186381304971664636885725485 69892989364374238832147057)
                  ·
                    refine ⟨52419742023280679124110293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69892989364374238832147057 52419742023280679124110293)
                    ·
                      refine ⟨1228587703670640916971335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52419742023280679124110293 1228587703670640916971335)
                      ·
                        rfl

theorem cell23_2392666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_2392666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392666 prefixEnd_2392666 := by exact prefixLift 2392666
  have htrace : WordTrace (prefixWord ++ tailWord_2392666) baseStart_2392666 baseEnd_2392666 := by
    simpa [prefixWord, tailWord_2392666, baseEnd_2392666] using wordTrace_append hprefix tailTrace_2392666
  have hstable : (prefixWord ++ tailWord_2392666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392666).length < 2 ^ (prefixWord ++ tailWord_2392666).sum := by decide
  have hdescent : baseEnd_2392666 < baseStart_2392666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392690 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 7]
def baseStart_2392690 : Nat := 118140960795 + 2392690 * 2 ^ 59
def prefixEnd_2392690 : Nat := 4983230072969 + 3 ^ 40 * 2392690 * 2
def baseEnd_2392690 : Nat := 136511114134038758119025

theorem tailTrace_2392690 : CollatzResearch.WordTrace tailWord_2392690 prefixEnd_2392690 136511114134038758119025 := by
  unfold tailWord_2392690
  simp only [CollatzResearch.WordTrace]
  refine ⟨21817143425425060940925881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58179049134466829175802349 21817143425425060940925881)
  ·
    refine ⟨16362857569068795705694411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21817143425425060940925881 16362857569068795705694411)
    ·
      refine ⟨24544286353603193558541617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16362857569068795705694411 24544286353603193558541617)
      ·
        refine ⟨18408214765202395168906213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24544286353603193558541617 18408214765202395168906213)
        ·
          refine ⟨3451540268475449094169915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18408214765202395168906213 3451540268475449094169915)
          ·
            refine ⟨5177310402713173641254873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3451540268475449094169915 5177310402713173641254873)
            ·
              refine ⟨3882982802034880230941155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5177310402713173641254873 3882982802034880230941155)
              ·
                refine ⟨5824474203052320346411733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882982802034880230941155 5824474203052320346411733)
                ·
                  refine ⟨136511114134038758119025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5824474203052320346411733 136511114134038758119025)
                  ·
                    rfl

theorem cell23_2392690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_2392690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392690 prefixEnd_2392690 := by exact prefixLift 2392690
  have htrace : WordTrace (prefixWord ++ tailWord_2392690) baseStart_2392690 baseEnd_2392690 := by
    simpa [prefixWord, tailWord_2392690, baseEnd_2392690] using wordTrace_append hprefix tailTrace_2392690
  have hstable : (prefixWord ++ tailWord_2392690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392690).length < 2 ^ (prefixWord ++ tailWord_2392690).sum := by decide
  have hdescent : baseEnd_2392690 < baseStart_2392690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392701 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 2, 2, 2]
def baseStart_2392701 : Nat := 118140960795 + 2392701 * 2 ^ 59
def prefixEnd_2392701 : Nat := 4983230072969 + 3 ^ 40 * 2392701 * 2
def baseEnd_2392701 : Nat := 1228605675493548280033675

theorem tailTrace_2392701 : CollatzResearch.WordTrace tailWord_2392701 prefixEnd_2392701 1228605675493548280033675 := by
  unfold tailWord_2392701
  simp only [CollatzResearch.WordTrace]
  refine ⟨87268974904660392642353957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58179316603106928428235971 87268974904660392642353957)
  ·
    refine ⟨16362932794623823620441367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87268974904660392642353957 16362932794623823620441367)
    ·
      refine ⟨24544399191935735430662051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16362932794623823620441367 24544399191935735430662051)
      ·
        refine ⟨36816598787903603145993077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24544399191935735430662051 36816598787903603145993077)
        ·
          refine ⟨3451556136365962794936851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36816598787903603145993077 3451556136365962794936851)
          ·
            refine ⟨5177334204548944192405277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3451556136365962794936851 5177334204548944192405277)
            ·
              refine ⟨1941500326705854072151979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5177334204548944192405277 1941500326705854072151979)
              ·
                refine ⟨2912250490058781108227969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941500326705854072151979 2912250490058781108227969)
                ·
                  refine ⟨2184187867544085831170977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2912250490058781108227969 2184187867544085831170977)
                  ·
                    refine ⟨1638140900658064373378233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2184187867544085831170977 1638140900658064373378233)
                    ·
                      refine ⟨1228605675493548280033675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638140900658064373378233 1228605675493548280033675)
                      ·
                        rfl

theorem cell23_2392701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_2392701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392701 prefixEnd_2392701 := by exact prefixLift 2392701
  have htrace : WordTrace (prefixWord ++ tailWord_2392701) baseStart_2392701 baseEnd_2392701 := by
    simpa [prefixWord, tailWord_2392701, baseEnd_2392701] using wordTrace_append hprefix tailTrace_2392701
  have hstable : (prefixWord ++ tailWord_2392701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392701).length < 2 ^ (prefixWord ++ tailWord_2392701).sum := by decide
  have hdescent : baseEnd_2392701 < baseStart_2392701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392724 : List Nat := [2, 4, 2, 2, 1, 3, 1, 3, 5]
def baseStart_2392724 : Nat := 118140960795 + 2392724 * 2 ^ 59
def prefixEnd_2392724 : Nat := 4983230072969 + 3 ^ 40 * 2392724 * 2
def baseEnd_2392724 : Nat := 136513053949844632227341

theorem tailTrace_2392724 : CollatzResearch.WordTrace tailWord_2392724 prefixEnd_2392724 136513053949844632227341 := by
  unfold tailWord_2392724
  simp only [CollatzResearch.WordTrace]
  refine ⟨43634906891788533785220613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58179875855718045046960817 43634906891788533785220613)
  ·
    refine ⟨8181545042210350084728865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43634906891788533785220613 8181545042210350084728865)
    ·
      refine ⟨6136158781657762563546649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8181545042210350084728865 6136158781657762563546649)
      ·
        refine ⟨4602119086243321922659987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6136158781657762563546649 4602119086243321922659987)
        ·
          refine ⟨6903178629364982883989981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4602119086243321922659987 6903178629364982883989981)
          ·
            refine ⟨2588691986011868581496243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6903178629364982883989981 2588691986011868581496243)
            ·
              refine ⟨3883037979017802872244365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2588691986011868581496243 3883037979017802872244365)
              ·
                refine ⟨1456139242131676077091637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3883037979017802872244365 1456139242131676077091637)
                ·
                  refine ⟨136513053949844632227341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1456139242131676077091637 136513053949844632227341)
                  ·
                    rfl

theorem cell23_2392724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_2392724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392724 prefixEnd_2392724 := by exact prefixLift 2392724
  have htrace : WordTrace (prefixWord ++ tailWord_2392724) baseStart_2392724 baseEnd_2392724 := by
    simpa [prefixWord, tailWord_2392724, baseEnd_2392724] using wordTrace_append hprefix tailTrace_2392724
  have hstable : (prefixWord ++ tailWord_2392724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392724).length < 2 ^ (prefixWord ++ tailWord_2392724).sum := by decide
  have hdescent : baseEnd_2392724 < baseStart_2392724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392740 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_2392740 : Nat := 118140960795 + 2392740 * 2 ^ 59
def prefixEnd_2392740 : Nat := 4983230072969 + 3 ^ 40 * 2392740 * 2
def baseEnd_2392740 : Nat := 1228625701239073627445995

theorem tailTrace_2392740 : CollatzResearch.WordTrace tailWord_2392740 prefixEnd_2392740 1228625701239073627445995 := by
  unfold tailWord_2392740
  simp only [CollatzResearch.WordTrace]
  refine ⟨43635198675759551151511837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58180264901012734868682449 43635198675759551151511837)
  ·
    refine ⟨16363199503409831681816939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43635198675759551151511837 16363199503409831681816939)
    ·
      refine ⟨24544799255114747522725409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16363199503409831681816939 24544799255114747522725409)
      ·
        refine ⟨18408599441336060642044057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24544799255114747522725409 18408599441336060642044057)
        ·
          refine ⟨13806449581002045481533043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18408599441336060642044057 13806449581002045481533043)
          ·
            refine ⟨20709674371503068222299565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13806449581002045481533043 20709674371503068222299565)
            ·
              refine ⟨7766127889313650583362337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20709674371503068222299565 7766127889313650583362337)
              ·
                refine ⟨5824595916985237937521753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7766127889313650583362337 5824595916985237937521753)
                ·
                  refine ⟨4368446937738928453141315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5824595916985237937521753 4368446937738928453141315)
                  ·
                    refine ⟨6552670406608392679711973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4368446937738928453141315 6552670406608392679711973)
                    ·
                      refine ⟨1228625701239073627445995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6552670406608392679711973 1228625701239073627445995)
                      ·
                        rfl

theorem cell23_2392740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_2392740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392740 prefixEnd_2392740 := by exact prefixLift 2392740
  have htrace : WordTrace (prefixWord ++ tailWord_2392740) baseStart_2392740 baseEnd_2392740 := by
    simpa [prefixWord, tailWord_2392740, baseEnd_2392740] using wordTrace_append hprefix tailTrace_2392740
  have hstable : (prefixWord ++ tailWord_2392740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392740).length < 2 ^ (prefixWord ++ tailWord_2392740).sum := by decide
  have hdescent : baseEnd_2392740 < baseStart_2392740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392800 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 3, 5, 2]
def baseStart_2392800 : Nat := 118140960795 + 2392800 * 2 ^ 59
def prefixEnd_2392800 : Nat := 4983230072969 + 3 ^ 40 * 2392800 * 2
def baseEnd_2392800 : Nat := 1228656510078343392695719

theorem tailTrace_2392800 : CollatzResearch.WordTrace tailWord_2392800 prefixEnd_2392800 1228656510078343392695719 := by
  unfold tailWord_2392800
  simp only [CollatzResearch.WordTrace]
  refine ⟨43636292865650866275103927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58181723820867821700138569 43636292865650866275103927)
  ·
    refine ⟨65454439298476299412655891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43636292865650866275103927 65454439298476299412655891)
    ·
      refine ⟨98181658947714449118983837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65454439298476299412655891 98181658947714449118983837)
      ·
        refine ⟨36818122105392918419618939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98181658947714449118983837 36818122105392918419618939)
        ·
          refine ⟨55227183158089377629428409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36818122105392918419618939 55227183158089377629428409)
          ·
            refine ⟨41420387368567033222071307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55227183158089377629428409 41420387368567033222071307)
            ·
              refine ⟨62130581052850549833106961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41420387368567033222071307 62130581052850549833106961)
              ·
                refine ⟨46597935789637912374830221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62130581052850549833106961 46597935789637912374830221)
                ·
                  refine ⟨17474225921114217140561333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46597935789637912374830221 17474225921114217140561333)
                  ·
                    refine ⟨1638208680104457856927625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17474225921114217140561333 1638208680104457856927625)
                    ·
                      refine ⟨1228656510078343392695719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638208680104457856927625 1228656510078343392695719)
                      ·
                        rfl

theorem cell23_2392800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_2392800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392800 prefixEnd_2392800 := by exact prefixLift 2392800
  have htrace : WordTrace (prefixWord ++ tailWord_2392800) baseStart_2392800 baseEnd_2392800 := by
    simpa [prefixWord, tailWord_2392800, baseEnd_2392800] using wordTrace_append hprefix tailTrace_2392800
  have hstable : (prefixWord ++ tailWord_2392800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392800).length < 2 ^ (prefixWord ++ tailWord_2392800).sum := by decide
  have hdescent : baseEnd_2392800 < baseStart_2392800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392801 : List Nat := [1, 2, 3, 1, 4, 3, 2, 2, 1, 4]
def baseStart_2392801 : Nat := 118140960795 + 2392801 * 2 ^ 59
def prefixEnd_2392801 : Nat := 4983230072969 + 3 ^ 40 * 2392801 * 2
def baseEnd_2392801 : Nat := 409552341186332629594405

theorem tailTrace_2392801 : CollatzResearch.WordTrace tailWord_2392801 prefixEnd_2392801 409552341186332629594405 := by
  unfold tailWord_2392801
  simp only [CollatzResearch.WordTrace]
  refine ⟨87272622204298109720994257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58181748136198739813996171 87272622204298109720994257)
  ·
    refine ⟨65454466653223582290745693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87272622204298109720994257 65454466653223582290745693)
    ·
      refine ⟨24545424994958843359029635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65454466653223582290745693 24545424994958843359029635)
      ·
        refine ⟨36818137492438265038544453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24545424994958843359029635 36818137492438265038544453)
        ·
          refine ⟨6903400779832174694727085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36818137492438265038544453 6903400779832174694727085)
          ·
            refine ⟨2588775292437065510522657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6903400779832174694727085 2588775292437065510522657)
            ·
              refine ⟨1941581469327799132891993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2588775292437065510522657 1941581469327799132891993)
              ·
                refine ⟨1456186101995849349668995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1941581469327799132891993 1456186101995849349668995)
                ·
                  refine ⟨2184279152993774024503493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456186101995849349668995 2184279152993774024503493)
                  ·
                    refine ⟨409552341186332629594405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2184279152993774024503493 409552341186332629594405)
                    ·
                      rfl

theorem cell23_2392801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_2392801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392801 prefixEnd_2392801 := by exact prefixLift 2392801
  have htrace : WordTrace (prefixWord ++ tailWord_2392801) baseStart_2392801 baseEnd_2392801 := by
    simpa [prefixWord, tailWord_2392801, baseEnd_2392801] using wordTrace_append hprefix tailTrace_2392801
  have hstable : (prefixWord ++ tailWord_2392801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392801).length < 2 ^ (prefixWord ++ tailWord_2392801).sum := by decide
  have hdescent : baseEnd_2392801 < baseStart_2392801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392834 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_2392834 : Nat := 118140960795 + 2392834 * 2 ^ 59
def prefixEnd_2392834 : Nat := 4983230072969 + 3 ^ 40 * 2392834 * 2
def baseEnd_2392834 : Nat := 1228673968420596259670563

theorem tailTrace_2392834 : CollatzResearch.WordTrace tailWord_2392834 prefixEnd_2392834 1228673968420596259670563 := by
  unfold tailWord_2392834
  simp only [CollatzResearch.WordTrace]
  refine ⟨21818456453294639089236389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58182550542119037571297037 21818456453294639089236389)
  ·
    refine ⟨4090960584992744829231823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21818456453294639089236389 4090960584992744829231823)
    ·
      refine ⟨6136440877489117243847735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4090960584992744829231823 6136440877489117243847735)
      ·
        refine ⟨9204661316233675865771603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6136440877489117243847735 9204661316233675865771603)
        ·
          refine ⟨13806991974350513798657405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9204661316233675865771603 13806991974350513798657405)
          ·
            refine ⟨5177621990381442674496527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13806991974350513798657405 5177621990381442674496527)
            ·
              refine ⟨7766432985572164011744791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5177621990381442674496527 7766432985572164011744791)
              ·
                refine ⟨11649649478358246017617187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7766432985572164011744791 11649649478358246017617187)
                ·
                  refine ⟨17474474217537369026425781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11649649478358246017617187 17474474217537369026425781)
                  ·
                    refine ⟨1638231957894128346227417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17474474217537369026425781 1638231957894128346227417)
                    ·
                      refine ⟨1228673968420596259670563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638231957894128346227417 1228673968420596259670563)
                      ·
                        rfl

theorem cell23_2392834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_2392834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392834 prefixEnd_2392834 := by exact prefixLift 2392834
  have htrace : WordTrace (prefixWord ++ tailWord_2392834) baseStart_2392834 baseEnd_2392834 := by
    simpa [prefixWord, tailWord_2392834, baseEnd_2392834] using wordTrace_append hprefix tailTrace_2392834
  have hstable : (prefixWord ++ tailWord_2392834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392834).length < 2 ^ (prefixWord ++ tailWord_2392834).sum := by decide
  have hdescent : baseEnd_2392834 < baseStart_2392834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392840 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 1, 6]
def baseStart_2392840 : Nat := 118140960795 + 2392840 * 2 ^ 59
def prefixEnd_2392840 : Nat := 4983230072969 + 3 ^ 40 * 2392840 * 2
def baseEnd_2392840 : Nat := 409559016434841078731845

theorem tailTrace_2392840 : CollatzResearch.WordTrace tailWord_2392840 prefixEnd_2392840 409559016434841078731845 := by
  unfold tailWord_2392840
  simp only [CollatzResearch.WordTrace]
  refine ⟨43637022325578409690831987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58182696434104546254442649 43637022325578409690831987)
  ·
    refine ⟨65455533488367614536247981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43637022325578409690831987 65455533488367614536247981)
    ·
      refine ⟨24545825058137855451092993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65455533488367614536247981 24545825058137855451092993)
      ·
        refine ⟨18409368793603391588319745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24545825058137855451092993 18409368793603391588319745)
        ·
          refine ⟨13807026595202543691239809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18409368793603391588319745 13807026595202543691239809)
          ·
            refine ⟨10355269946401907768429857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13807026595202543691239809 10355269946401907768429857)
            ·
              refine ⟨7766452459801430826322393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10355269946401907768429857 7766452459801430826322393)
              ·
                refine ⟨5824839344851073119741795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7766452459801430826322393 5824839344851073119741795)
                ·
                  refine ⟨8737259017276609679612693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5824839344851073119741795 8737259017276609679612693)
                  ·
                    refine ⟨409559016434841078731845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8737259017276609679612693 409559016434841078731845)
                    ·
                      rfl

theorem cell23_2392840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_2392840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392840 prefixEnd_2392840 := by exact prefixLift 2392840
  have htrace : WordTrace (prefixWord ++ tailWord_2392840) baseStart_2392840 baseEnd_2392840 := by
    simpa [prefixWord, tailWord_2392840, baseEnd_2392840] using wordTrace_append hprefix tailTrace_2392840
  have hstable : (prefixWord ++ tailWord_2392840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392840).length < 2 ^ (prefixWord ++ tailWord_2392840).sum := by decide
  have hdescent : baseEnd_2392840 < baseStart_2392840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392843 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 6]
def baseStart_2392843 : Nat := 118140960795 + 2392843 * 2 ^ 59
def prefixEnd_2392843 : Nat := 4983230072969 + 3 ^ 40 * 2392843 * 2
def baseEnd_2392843 : Nat := 1228678589746486724458021

theorem tailTrace_2392843 : CollatzResearch.WordTrace tailWord_2392843 prefixEnd_2392843 1228678589746486724458021 := by
  unfold tailWord_2392843
  simp only [CollatzResearch.WordTrace]
  refine ⟨87274154070145950894023183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58182769380097300596015455 87274154070145950894023183)
  ·
    refine ⟨130911231105218926341034775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87274154070145950894023183 130911231105218926341034775)
    ·
      refine ⟨196366846657828389511552163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130911231105218926341034775 196366846657828389511552163)
      ·
        refine ⟨294550269986742584267328245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196366846657828389511552163 294550269986742584267328245)
        ·
          refine ⟨27614087811257117275062023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 294550269986742584267328245 27614087811257117275062023)
          ·
            refine ⟨41421131716885675912593035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27614087811257117275062023 41421131716885675912593035)
            ·
              refine ⟨62131697575328513868889553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41421131716885675912593035 62131697575328513868889553)
              ·
                refine ⟨46598773181496385401667165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62131697575328513868889553 46598773181496385401667165)
                ·
                  refine ⟨17474539943061144525625187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46598773181496385401667165 17474539943061144525625187)
                  ·
                    refine ⟨26211809914591716788437781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17474539943061144525625187 26211809914591716788437781)
                    ·
                      refine ⟨1228678589746486724458021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26211809914591716788437781 1228678589746486724458021)
                      ·
                        rfl

theorem cell23_2392843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_2392843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392843 prefixEnd_2392843 := by exact prefixLift 2392843
  have htrace : WordTrace (prefixWord ++ tailWord_2392843) baseStart_2392843 baseEnd_2392843 := by
    simpa [prefixWord, tailWord_2392843, baseEnd_2392843] using wordTrace_append hprefix tailTrace_2392843
  have hstable : (prefixWord ++ tailWord_2392843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392843).length < 2 ^ (prefixWord ++ tailWord_2392843).sum := by decide
  have hdescent : baseEnd_2392843 < baseStart_2392843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392847 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 5, 2, 2]
def baseStart_2392847 : Nat := 118140960795 + 2392847 * 2 ^ 59
def prefixEnd_2392847 : Nat := 4983230072969 + 3 ^ 40 * 2392847 * 2
def baseEnd_2392847 : Nat := 1228680643669104708808003

theorem tailTrace_2392847 : CollatzResearch.WordTrace tailWord_2392847 prefixEnd_2392847 1228680643669104708808003 := by
  unfold tailWord_2392847
  simp only [CollatzResearch.WordTrace]
  refine ⟨87274299962131459577168795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58182866641420973051445863 87274299962131459577168795)
  ·
    refine ⟨130911449943197189365753193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87274299962131459577168795 130911449943197189365753193)
    ·
      refine ⟨98183587457397892024314895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130911449943197189365753193 98183587457397892024314895)
      ·
        refine ⟨147275381186096838036472343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98183587457397892024314895 147275381186096838036472343)
        ·
          refine ⟨220913071779145257054708515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147275381186096838036472343 220913071779145257054708515)
          ·
            refine ⟨331369607668717885582062773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220913071779145257054708515 331369607668717885582062773)
            ·
              refine ⟨31065900718942301773318385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 331369607668717885582062773 31065900718942301773318385)
              ·
                refine ⟨23299425539206726329988789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31065900718942301773318385 23299425539206726329988789)
                ·
                  refine ⟨2184321144300630593436449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23299425539206726329988789 2184321144300630593436449)
                  ·
                    refine ⟨1638240858225472945077337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2184321144300630593436449 1638240858225472945077337)
                    ·
                      refine ⟨1228680643669104708808003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638240858225472945077337 1228680643669104708808003)
                      ·
                        rfl

theorem cell23_2392847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 2, 2].length) (baseStart_2392847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392847 prefixEnd_2392847 := by exact prefixLift 2392847
  have htrace : WordTrace (prefixWord ++ tailWord_2392847) baseStart_2392847 baseEnd_2392847 := by
    simpa [prefixWord, tailWord_2392847, baseEnd_2392847] using wordTrace_append hprefix tailTrace_2392847
  have hstable : (prefixWord ++ tailWord_2392847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392847).length < 2 ^ (prefixWord ++ tailWord_2392847).sum := by decide
  have hdescent : baseEnd_2392847 < baseStart_2392847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392853 : List Nat := [1, 3, 2, 1, 2, 2, 12]
def baseStart_2392853 : Nat := 118140960795 + 2392853 * 2 ^ 59
def prefixEnd_2392853 : Nat := 4983230072969 + 3 ^ 40 * 2392853 * 2
def baseEnd_2392853 : Nat := 15168934871025082534975

theorem tailTrace_2392853 : CollatzResearch.WordTrace tailWord_2392853 prefixEnd_2392853 15168934871025082534975 := by
  unfold tailWord_2392853
  simp only [CollatzResearch.WordTrace]
  refine ⟨87274518800109722601887213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58183012533406481734591475 87274518800109722601887213)
  ·
    refine ⟨32727944550041145975707705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87274518800109722601887213 32727944550041145975707705)
    ·
      refine ⟨24545958412530859481780779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32727944550041145975707705 24545958412530859481780779)
      ·
        refine ⟨36818937618796289222671169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24545958412530859481780779 36818937618796289222671169)
        ·
          refine ⟨27614203214097216917003377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36818937618796289222671169 27614203214097216917003377)
          ·
            refine ⟨20710652410572912687752533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27614203214097216917003377 20710652410572912687752533)
            ·
              refine ⟨15168934871025082534975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 20710652410572912687752533 15168934871025082534975)
              ·
                rfl

theorem cell23_2392853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 12].length) (baseStart_2392853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392853 prefixEnd_2392853 := by exact prefixLift 2392853
  have htrace : WordTrace (prefixWord ++ tailWord_2392853) baseStart_2392853 baseEnd_2392853 := by
    simpa [prefixWord, tailWord_2392853, baseEnd_2392853] using wordTrace_append hprefix tailTrace_2392853
  have hstable : (prefixWord ++ tailWord_2392853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392853).length < 2 ^ (prefixWord ++ tailWord_2392853).sum := by decide
  have hdescent : baseEnd_2392853 < baseStart_2392853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392864 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 3, 2, 2]
def baseStart_2392864 : Nat := 118140960795 + 2392864 * 2 ^ 59
def prefixEnd_2392864 : Nat := 4983230072969 + 3 ^ 40 * 2392864 * 2
def baseEnd_2392864 : Nat := 1228689372840231142295425

theorem tailTrace_2392864 : CollatzResearch.WordTrace tailWord_2392864 prefixEnd_2392864 1228689372840231142295425 := by
  unfold tailWord_2392864
  simp only [CollatzResearch.WordTrace]
  refine ⟨43637460001534935740268823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58183280002046580987025097 43637460001534935740268823)
  ·
    refine ⟨65456190002302403610403235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43637460001534935740268823 65456190002302403610403235)
    ·
      refine ⟨98184285003453605415604853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65456190002302403610403235 98184285003453605415604853)
      ·
        refine ⟨9204776719073775507712955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98184285003453605415604853 9204776719073775507712955)
        ·
          refine ⟨13807165078610663261569433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9204776719073775507712955 13807165078610663261569433)
          ·
            refine ⟨10355373808957997446177075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13807165078610663261569433 10355373808957997446177075)
            ·
              refine ⟨15533060713436996169265613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10355373808957997446177075 15533060713436996169265613)
              ·
                refine ⟨5824897767538873563474605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15533060713436996169265613 5824897767538873563474605)
                ·
                  refine ⟨2184336662827077586302977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5824897767538873563474605 2184336662827077586302977)
                  ·
                    refine ⟨1638252497120308189727233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2184336662827077586302977 1638252497120308189727233)
                    ·
                      refine ⟨1228689372840231142295425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638252497120308189727233 1228689372840231142295425)
                      ·
                        rfl

theorem cell23_2392864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_2392864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392864 prefixEnd_2392864 := by exact prefixLift 2392864
  have htrace : WordTrace (prefixWord ++ tailWord_2392864) baseStart_2392864 baseEnd_2392864 := by
    simpa [prefixWord, tailWord_2392864, baseEnd_2392864] using wordTrace_append hprefix tailTrace_2392864
  have hstable : (prefixWord ++ tailWord_2392864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392864).length < 2 ^ (prefixWord ++ tailWord_2392864).sum := by decide
  have hdescent : baseEnd_2392864 < baseStart_2392864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392873 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_2392873 : Nat := 118140960795 + 2392873 * 2 ^ 59
def prefixEnd_2392873 : Nat := 4983230072969 + 3 ^ 40 * 2392873 * 2
def baseEnd_2392873 : Nat := 1228693994166121607082883

theorem tailTrace_2392873 : CollatzResearch.WordTrace tailWord_2392873 prefixEnd_2392873 1228693994166121607082883 := by
  unfold tailWord_2392873
  simp only [CollatzResearch.WordTrace]
  refine ⟨87275248260037266017615273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58183498840024844011743515 87275248260037266017615273)
  ·
    refine ⟨65456436195027949513211455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87275248260037266017615273 65456436195027949513211455)
    ·
      refine ⟨98184654292541924269817183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65456436195027949513211455 98184654292541924269817183)
      ·
        refine ⟨147276981438812886404725775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98184654292541924269817183 147276981438812886404725775)
        ·
          refine ⟨220915472158219329607088663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147276981438812886404725775 220915472158219329607088663)
          ·
            refine ⟨331373208237328994410632995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220915472158219329607088663 331373208237328994410632995)
            ·
              refine ⟨497059812355993491615949493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331373208237328994410632995 497059812355993491615949493)
              ·
                refine ⟨46599357408374389838995265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 497059812355993491615949493 46599357408374389838995265)
                ·
                  refine ⟨34949518056280792379246449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46599357408374389838995265 34949518056280792379246449)
                  ·
                    refine ⟨26212138542210594284434837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34949518056280792379246449 26212138542210594284434837)
                    ·
                      refine ⟨1228693994166121607082883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26212138542210594284434837 1228693994166121607082883)
                      ·
                        rfl

theorem cell23_2392873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_2392873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392873 prefixEnd_2392873 := by exact prefixLift 2392873
  have htrace : WordTrace (prefixWord ++ tailWord_2392873) baseStart_2392873 baseEnd_2392873 := by
    simpa [prefixWord, tailWord_2392873, baseEnd_2392873] using wordTrace_append hprefix tailTrace_2392873
  have hstable : (prefixWord ++ tailWord_2392873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392873).length < 2 ^ (prefixWord ++ tailWord_2392873).sum := by decide
  have hdescent : baseEnd_2392873 < baseStart_2392873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392914 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_2392914 : Nat := 118140960795 + 2392914 * 2 ^ 59
def prefixEnd_2392914 : Nat := 4983230072969 + 3 ^ 40 * 2392914 * 2
def baseEnd_2392914 : Nat := 1228715046872955946670195

theorem tailTrace_2392914 : CollatzResearch.WordTrace tailWord_2392914 prefixEnd_2392914 1228715046872955946670195 := by
  unfold tailWord_2392914
  simp only [CollatzResearch.WordTrace]
  refine ⟨21819185913222182504964449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58184495768592486679905197 21819185913222182504964449)
  ·
    refine ⟨16364389434916636878723337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21819185913222182504964449 16364389434916636878723337)
    ·
      refine ⟨12273292076187477659042503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16364389434916636878723337 12273292076187477659042503)
      ·
        refine ⟨18409938114281216488563755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12273292076187477659042503 18409938114281216488563755)
        ·
          refine ⟨27614907171421824732845633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18409938114281216488563755 27614907171421824732845633)
          ·
            refine ⟨20711180378566368549634225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27614907171421824732845633 20711180378566368549634225)
            ·
              refine ⟨15533385283924776412225669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20711180378566368549634225 15533385283924776412225669)
              ·
                refine ⟨2912509740735895577292313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15533385283924776412225669 2912509740735895577292313)
                ·
                  refine ⟨2184382305551921682969235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2912509740735895577292313 2184382305551921682969235)
                  ·
                    refine ⟨3276573458327882524453853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2184382305551921682969235 3276573458327882524453853)
                    ·
                      refine ⟨1228715046872955946670195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3276573458327882524453853 1228715046872955946670195)
                      ·
                        rfl

theorem cell23_2392914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_2392914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392914 prefixEnd_2392914 := by exact prefixLift 2392914
  have htrace : WordTrace (prefixWord ++ tailWord_2392914) baseStart_2392914 baseEnd_2392914 := by
    simpa [prefixWord, tailWord_2392914, baseEnd_2392914] using wordTrace_append hprefix tailTrace_2392914
  have hstable : (prefixWord ++ tailWord_2392914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392914).length < 2 ^ (prefixWord ++ tailWord_2392914).sum := by decide
  have hdescent : baseEnd_2392914 < baseStart_2392914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392931 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 2, 1, 3]
def baseStart_2392931 : Nat := 118140960795 + 2392931 * 2 ^ 59
def prefixEnd_2392931 : Nat := 4983230072969 + 3 ^ 40 * 2392931 * 2
def baseEnd_2392931 : Nat := 1228723776044082380157617

theorem tailTrace_2392931 : CollatzResearch.WordTrace tailWord_2392931 prefixEnd_2392931 1228723776044082380157617 := by
  unfold tailWord_2392931
  simp only [CollatzResearch.WordTrace]
  refine ⟨87277363693827141923226647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58184909129218094615484431 87277363693827141923226647)
  ·
    refine ⟨130916045540740712884839971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87277363693827141923226647 130916045540740712884839971)
    ·
      refine ⟨196374068311111069327259957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130916045540740712884839971 196374068311111069327259957)
      ·
        refine ⟨18410068904166662749430621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 196374068311111069327259957 18410068904166662749430621)
        ·
          refine ⟨6903775839062498531036483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18410068904166662749430621 6903775839062498531036483)
          ·
            refine ⟨10355663758593747796554725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6903775839062498531036483 10355663758593747796554725)
            ·
              refine ⟨1941686954736327711854011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10355663758593747796554725 1941686954736327711854011)
              ·
                refine ⟨2912530432104491567781017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941686954736327711854011 2912530432104491567781017)
                ·
                  refine ⟨2184397824078368675835763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2912530432104491567781017 2184397824078368675835763)
                  ·
                    refine ⟨3276596736117553013753645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2184397824078368675835763 3276596736117553013753645)
                    ·
                      refine ⟨1228723776044082380157617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3276596736117553013753645 1228723776044082380157617)
                      ·
                        rfl

theorem cell23_2392931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_2392931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392931 prefixEnd_2392931 := by exact prefixLift 2392931
  have htrace : WordTrace (prefixWord ++ tailWord_2392931) baseStart_2392931 baseEnd_2392931 := by
    simpa [prefixWord, tailWord_2392931, baseEnd_2392931] using wordTrace_append hprefix tailTrace_2392931
  have hstable : (prefixWord ++ tailWord_2392931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392931).length < 2 ^ (prefixWord ++ tailWord_2392931).sum := by decide
  have hdescent : baseEnd_2392931 < baseStart_2392931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2392940 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_2392940 : Nat := 118140960795 + 2392940 * 2 ^ 59
def prefixEnd_2392940 : Nat := 4983230072969 + 3 ^ 40 * 2392940 * 2
def baseEnd_2392940 : Nat := 1228728397369972844945075

theorem tailTrace_2392940 : CollatzResearch.WordTrace tailWord_2392940 prefixEnd_2392940 1228728397369972844945075 := by
  unfold tailWord_2392940
  simp only [CollatzResearch.WordTrace]
  refine ⟨43638845975397268230152137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58185127967196357640202849 43638845975397268230152137)
  ·
    refine ⟨32729134481547951172614103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43638845975397268230152137 32729134481547951172614103)
    ·
      refine ⟨49093701722321926758921155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32729134481547951172614103 49093701722321926758921155)
      ·
        refine ⟨73640552583482890138381733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49093701722321926758921155 73640552583482890138381733)
        ·
          refine ⟨13807603609403041900946575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73640552583482890138381733 13807603609403041900946575)
          ·
            refine ⟨20711405414104562851419863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13807603609403041900946575 20711405414104562851419863)
            ·
              refine ⟨31067108121156844277129795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20711405414104562851419863 31067108121156844277129795)
              ·
                refine ⟨46600662181735266415694693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31067108121156844277129795 46600662181735266415694693)
                ·
                  refine ⟨8737624159075362452942755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46600662181735266415694693 8737624159075362452942755)
                  ·
                    refine ⟨13106436238613043679414133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8737624159075362452942755 13106436238613043679414133)
                    ·
                      refine ⟨1228728397369972844945075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13106436238613043679414133 1228728397369972844945075)
                      ·
                        rfl

theorem cell23_2392940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_2392940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2392940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2392940 prefixEnd_2392940 := by exact prefixLift 2392940
  have htrace : WordTrace (prefixWord ++ tailWord_2392940) baseStart_2392940 baseEnd_2392940 := by
    simpa [prefixWord, tailWord_2392940, baseEnd_2392940] using wordTrace_append hprefix tailTrace_2392940
  have hstable : (prefixWord ++ tailWord_2392940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2392940).length < 2 ^ (prefixWord ++ tailWord_2392940).sum := by decide
  have hdescent : baseEnd_2392940 < baseStart_2392940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2392940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393027 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 3, 6, 2]
def baseStart_2393027 : Nat := 118140960795 + 2393027 * 2 ^ 59
def prefixEnd_2393027 : Nat := 4983230072969 + 3 ^ 40 * 2393027 * 2
def baseEnd_2393027 : Nat := 1228773070186914004557175

theorem tailTrace_2393027 : CollatzResearch.WordTrace tailWord_2393027 prefixEnd_2393027 1228773070186914004557175 := by
  unfold tailWord_2393027
  simp only [CollatzResearch.WordTrace]
  refine ⟨87280865101479350318721335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58187243400986233545814223 87280865101479350318721335)
  ·
    refine ⟨130921297652219025478082003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87280865101479350318721335 130921297652219025478082003)
    ·
      refine ⟨196381946478328538217123005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130921297652219025478082003 196381946478328538217123005)
      ·
        refine ⟨73643229929373201831421127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196381946478328538217123005 73643229929373201831421127)
        ·
          refine ⟨110464844894059802747131691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73643229929373201831421127 110464844894059802747131691)
          ·
            refine ⟨165697267341089704120697537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110464844894059802747131691 165697267341089704120697537)
            ·
              refine ⟨124272950505817278090523153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165697267341089704120697537 124272950505817278090523153)
              ·
                refine ⟨93204712879362958567892365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124272950505817278090523153 93204712879362958567892365)
                ·
                  refine ⟨34951767329761109462959637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93204712879362958567892365 34951767329761109462959637)
                  ·
                    refine ⟨1638364093582552006076233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34951767329761109462959637 1638364093582552006076233)
                    ·
                      refine ⟨1228773070186914004557175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638364093582552006076233 1228773070186914004557175)
                      ·
                        rfl

theorem cell23_2393027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 6, 2].length) (baseStart_2393027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393027 prefixEnd_2393027 := by exact prefixLift 2393027
  have htrace : WordTrace (prefixWord ++ tailWord_2393027) baseStart_2393027 baseEnd_2393027 := by
    simpa [prefixWord, tailWord_2393027, baseEnd_2393027] using wordTrace_append hprefix tailTrace_2393027
  have hstable : (prefixWord ++ tailWord_2393027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393027).length < 2 ^ (prefixWord ++ tailWord_2393027).sum := by decide
  have hdescent : baseEnd_2393027 < baseStart_2393027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393040 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_2393040 : Nat := 118140960795 + 2393040 * 2 ^ 59
def prefixEnd_2393040 : Nat := 4983230072969 + 3 ^ 40 * 2393040 * 2
def baseEnd_2393040 : Nat := 1228779745435422453694615

theorem tailTrace_2393040 : CollatzResearch.WordTrace tailWord_2393040 prefixEnd_2393040 1228779745435422453694615 := by
  unfold tailWord_2393040
  simp only [CollatzResearch.WordTrace]
  refine ⟨43640669625216126769472287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58187559500288169025963049 43640669625216126769472287)
  ·
    refine ⟨65461004437824190154208431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43640669625216126769472287 65461004437824190154208431)
    ·
      refine ⟨98191506656736285231312647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65461004437824190154208431 98191506656736285231312647)
      ·
        refine ⟨147287259985104427846968971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98191506656736285231312647 147287259985104427846968971)
        ·
          refine ⟨220930889977656641770453457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147287259985104427846968971 220930889977656641770453457)
          ·
            refine ⟨165698167483242481327840093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220930889977656641770453457 165698167483242481327840093)
            ·
              refine ⟨62136812806215930497940035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165698167483242481327840093 62136812806215930497940035)
              ·
                refine ⟨93205219209323895746910053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62136812806215930497940035 93205219209323895746910053)
                ·
                  refine ⟨17475978601748230452545635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93205219209323895746910053 17475978601748230452545635)
                  ·
                    refine ⟨26213967902622345678818453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17475978601748230452545635 26213967902622345678818453)
                    ·
                      refine ⟨1228779745435422453694615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26213967902622345678818453 1228779745435422453694615)
                      ·
                        rfl

theorem cell23_2393040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_2393040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393040 prefixEnd_2393040 := by exact prefixLift 2393040
  have htrace : WordTrace (prefixWord ++ tailWord_2393040) baseStart_2393040 baseEnd_2393040 := by
    simpa [prefixWord, tailWord_2393040, baseEnd_2393040] using wordTrace_append hprefix tailTrace_2393040
  have hstable : (prefixWord ++ tailWord_2393040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393040).length < 2 ^ (prefixWord ++ tailWord_2393040).sum := by decide
  have hdescent : baseEnd_2393040 < baseStart_2393040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393047 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 3]
def baseStart_2393047 : Nat := 118140960795 + 2393047 * 2 ^ 59
def prefixEnd_2393047 : Nat := 4983230072969 + 3 ^ 40 * 2393047 * 2
def baseEnd_2393047 : Nat := 1228783339800003926307083

theorem tailTrace_2393047 : CollatzResearch.WordTrace tailWord_2393047 prefixEnd_2393047 1228783339800003926307083 := by
  unfold tailWord_2393047
  simp only [CollatzResearch.WordTrace]
  refine ⟨87281594561406893734449395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58187729707604595822966263 87281594561406893734449395)
  ·
    refine ⟨130922391842110340601674093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87281594561406893734449395 130922391842110340601674093)
    ·
      refine ⟨49095896940791377725627785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130922391842110340601674093 49095896940791377725627785)
      ·
        refine ⟨36821922705593533294220839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49095896940791377725627785 36821922705593533294220839)
        ·
          refine ⟨55232884058390299941331259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36821922705593533294220839 55232884058390299941331259)
          ·
            refine ⟨82849326087585449911996889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55232884058390299941331259 82849326087585449911996889)
            ·
              refine ⟨62136994565689087433997667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82849326087585449911996889 62136994565689087433997667)
              ·
                refine ⟨93205491848533631150996501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62136994565689087433997667 93205491848533631150996501)
                ·
                  refine ⟨4369007430400013960202961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93205491848533631150996501 4369007430400013960202961)
                  ·
                    refine ⟨3276755572800010470152221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4369007430400013960202961 3276755572800010470152221)
                    ·
                      refine ⟨1228783339800003926307083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3276755572800010470152221 1228783339800003926307083)
                      ·
                        rfl

theorem cell23_2393047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_2393047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393047 prefixEnd_2393047 := by exact prefixLift 2393047
  have htrace : WordTrace (prefixWord ++ tailWord_2393047) baseStart_2393047 baseEnd_2393047 := by
    simpa [prefixWord, tailWord_2393047, baseEnd_2393047] using wordTrace_append hprefix tailTrace_2393047
  have hstable : (prefixWord ++ tailWord_2393047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393047).length < 2 ^ (prefixWord ++ tailWord_2393047).sum := by decide
  have hdescent : baseEnd_2393047 < baseStart_2393047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393071 : List Nat := [1, 1, 2, 1, 4, 3, 3, 3, 1, 4]
def baseStart_2393071 : Nat := 118140960795 + 2393071 * 2 ^ 59
def prefixEnd_2393071 : Nat := 4983230072969 + 3 ^ 40 * 2393071 * 2
def baseEnd_2393071 : Nat := 409598554445237277468991

theorem tailTrace_2393071 : CollatzResearch.WordTrace tailWord_2393071 prefixEnd_2393071 409598554445237277468991 := by
  unfold tailWord_2393071
  simp only [CollatzResearch.WordTrace]
  refine ⟨87282469913319945833323067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58188313275546630555548711 87282469913319945833323067)
  ·
    refine ⟨130923704869979918749984601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87282469913319945833323067 130923704869979918749984601)
    ·
      refine ⟨98192778652484939062488451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130923704869979918749984601 98192778652484939062488451)
      ·
        refine ⟨147289167978727408593732677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98192778652484939062488451 147289167978727408593732677)
        ·
          refine ⟨27616718996011389111324877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147289167978727408593732677 27616718996011389111324877)
          ·
            refine ⟨10356269623504270916746829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27616718996011389111324877 10356269623504270916746829)
            ·
              refine ⟨3883601108814101593780061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10356269623504270916746829 3883601108814101593780061)
              ·
                refine ⟨1456350415805288097667523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3883601108814101593780061 1456350415805288097667523)
                ·
                  refine ⟨2184525623707932146501285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456350415805288097667523 2184525623707932146501285)
                  ·
                    refine ⟨409598554445237277468991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2184525623707932146501285 409598554445237277468991)
                    ·
                      rfl

theorem cell23_2393071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 1, 4].length) (baseStart_2393071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393071 prefixEnd_2393071 := by exact prefixLift 2393071
  have htrace : WordTrace (prefixWord ++ tailWord_2393071) baseStart_2393071 baseEnd_2393071 := by
    simpa [prefixWord, tailWord_2393071, baseEnd_2393071] using wordTrace_append hprefix tailTrace_2393071
  have hstable : (prefixWord ++ tailWord_2393071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393071).length < 2 ^ (prefixWord ++ tailWord_2393071).sum := by decide
  have hdescent : baseEnd_2393071 < baseStart_2393071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393121 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 2, 3, 2]
def baseStart_2393121 : Nat := 118140960795 + 2393121 * 2 ^ 59
def prefixEnd_2393121 : Nat := 4983230072969 + 3 ^ 40 * 2393121 * 2
def baseEnd_2393121 : Nat := 1228821337368436636781743

theorem tailTrace_2393121 : CollatzResearch.WordTrace tailWord_2393121 prefixEnd_2393121 1228821337368436636781743 := by
  unfold tailWord_2393121
  simp only [CollatzResearch.WordTrace]
  refine ⟨87284293563138804372643217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58189529042092536248428811 87284293563138804372643217)
  ·
    refine ⟨65463220172354103279482413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87284293563138804372643217 65463220172354103279482413)
    ·
      refine ⟨24548707564632788729805905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65463220172354103279482413 24548707564632788729805905)
      ·
        refine ⟨18411530673474591547354429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24548707564632788729805905 18411530673474591547354429)
        ·
          refine ⟨6904324002552971830257911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18411530673474591547354429 6904324002552971830257911)
          ·
            refine ⟨10356486003829457745386867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6904324002552971830257911 10356486003829457745386867)
            ·
              refine ⟨15534729005744186618080301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10356486003829457745386867 15534729005744186618080301)
              ·
                refine ⟨5825523377154069981780113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15534729005744186618080301 5825523377154069981780113)
                ·
                  refine ⟨4369142532865552486335085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5825523377154069981780113 4369142532865552486335085)
                  ·
                    refine ⟨1638428449824582182375657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4369142532865552486335085 1638428449824582182375657)
                    ·
                      refine ⟨1228821337368436636781743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638428449824582182375657 1228821337368436636781743)
                      ·
                        rfl

theorem cell23_2393121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_2393121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393121 prefixEnd_2393121 := by exact prefixLift 2393121
  have htrace : WordTrace (prefixWord ++ tailWord_2393121) baseStart_2393121 baseEnd_2393121 := by
    simpa [prefixWord, tailWord_2393121, baseEnd_2393121] using wordTrace_append hprefix tailTrace_2393121
  have hstable : (prefixWord ++ tailWord_2393121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393121).length < 2 ^ (prefixWord ++ tailWord_2393121).sum := by decide
  have hdescent : baseEnd_2393121 < baseStart_2393121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393145 : List Nat := [1, 2, 1, 5, 2, 1, 4, 2, 1, 1, 3]
def baseStart_2393145 : Nat := 118140960795 + 2393145 * 2 ^ 59
def prefixEnd_2393145 : Nat := 4983230072969 + 3 ^ 40 * 2393145 * 2
def baseEnd_2393145 : Nat := 1228833660904144542881633

theorem tailTrace_2393145 : CollatzResearch.WordTrace tailWord_2393145 prefixEnd_2393145 1228833660904144542881633 := by
  unfold tailWord_2393145
  simp only [CollatzResearch.WordTrace]
  refine ⟨87285168915051856471516889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58190112610034570981011259 87285168915051856471516889)
  ·
    refine ⟨65463876686288892353637667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87285168915051856471516889 65463876686288892353637667)
    ·
      refine ⟨98195815029433338530456501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65463876686288892353637667 98195815029433338530456501)
      ·
        refine ⟨9205857659009375487230297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98195815029433338530456501 9205857659009375487230297)
        ·
          refine ⟨6904393244257031615422723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9205857659009375487230297 6904393244257031615422723)
          ·
            refine ⟨10356589866385547423134085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6904393244257031615422723 10356589866385547423134085)
            ·
              refine ⟨1941860599947290141837641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10356589866385547423134085 1941860599947290141837641)
              ·
                refine ⟨1456395449960467606378231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1941860599947290141837641 1456395449960467606378231)
                ·
                  refine ⟨2184593174940701409567347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456395449960467606378231 2184593174940701409567347)
                  ·
                    refine ⟨3276889762411052114351021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2184593174940701409567347 3276889762411052114351021)
                    ·
                      refine ⟨1228833660904144542881633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3276889762411052114351021 1228833660904144542881633)
                      ·
                        rfl

theorem cell23_2393145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_2393145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393145 prefixEnd_2393145 := by exact prefixLift 2393145
  have htrace : WordTrace (prefixWord ++ tailWord_2393145) baseStart_2393145 baseEnd_2393145 := by
    simpa [prefixWord, tailWord_2393145, baseEnd_2393145] using wordTrace_append hprefix tailTrace_2393145
  have hstable : (prefixWord ++ tailWord_2393145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393145).length < 2 ^ (prefixWord ++ tailWord_2393145).sum := by decide
  have hdescent : baseEnd_2393145 < baseStart_2393145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393151 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 3, 2, 2]
def baseStart_2393151 : Nat := 118140960795 + 2393151 * 2 ^ 59
def prefixEnd_2393151 : Nat := 4983230072969 + 3 ^ 40 * 2393151 * 2
def baseEnd_2393151 : Nat := 1228836741788071519406605

theorem tailTrace_2393151 : CollatzResearch.WordTrace tailWord_2393151 prefixEnd_2393151 1228836741788071519406605 := by
  unfold tailWord_2393151
  simp only [CollatzResearch.WordTrace]
  refine ⟨87285387753030119496235307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58190258502020079664156871 87285387753030119496235307)
  ·
    refine ⟨130928081629545179244352961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87285387753030119496235307 130928081629545179244352961)
    ·
      refine ⟨98196061222158884433264721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130928081629545179244352961 98196061222158884433264721)
      ·
        refine ⟨73647045916619163324948541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98196061222158884433264721 73647045916619163324948541)
        ·
          refine ⟨27617642218732186246855703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73647045916619163324948541 27617642218732186246855703)
          ·
            refine ⟨41426463328098279370283555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27617642218732186246855703 41426463328098279370283555)
            ·
              refine ⟨62139694992147419055425333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41426463328098279370283555 62139694992147419055425333)
              ·
                refine ⟨5825596405513820536446125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62139694992147419055425333 5825596405513820536446125)
                ·
                  refine ⟨2184598652067682701167297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5825596405513820536446125 2184598652067682701167297)
                  ·
                    refine ⟨1638448989050762025875473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2184598652067682701167297 1638448989050762025875473)
                    ·
                      refine ⟨1228836741788071519406605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638448989050762025875473 1228836741788071519406605)
                      ·
                        rfl

theorem cell23_2393151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 2, 2].length) (baseStart_2393151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393151 prefixEnd_2393151 := by exact prefixLift 2393151
  have htrace : WordTrace (prefixWord ++ tailWord_2393151) baseStart_2393151 baseEnd_2393151 := by
    simpa [prefixWord, tailWord_2393151, baseEnd_2393151] using wordTrace_append hprefix tailTrace_2393151
  have hstable : (prefixWord ++ tailWord_2393151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393151).length < 2 ^ (prefixWord ++ tailWord_2393151).sum := by decide
  have hdescent : baseEnd_2393151 < baseStart_2393151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393157 : List Nat := [1, 3, 1, 1, 1, 3, 5, 8]
def baseStart_2393157 : Nat := 118140960795 + 2393157 * 2 ^ 59
def prefixEnd_2393157 : Nat := 4983230072969 + 3 ^ 40 * 2393157 * 2
def baseEnd_2393157 : Nat := 45512586024888833182651

theorem tailTrace_2393157 : CollatzResearch.WordTrace tailWord_2393157 prefixEnd_2393157 45512586024888833182651 := by
  unfold tailWord_2393157
  simp only [CollatzResearch.WordTrace]
  refine ⟨87285606591008382520953725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58190404394005588347302483 87285606591008382520953725)
  ·
    refine ⟨32732102471628143445357647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87285606591008382520953725 32732102471628143445357647)
    ·
      refine ⟨49098153707442215168036471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32732102471628143445357647 49098153707442215168036471)
      ·
        refine ⟨73647230561163322752054707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49098153707442215168036471 73647230561163322752054707)
        ·
          refine ⟨110470845841744984128082061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73647230561163322752054707 110470845841744984128082061)
          ·
            refine ⟨41426567190654369048030773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110470845841744984128082061 41426567190654369048030773)
            ·
              refine ⟨3883740674123847098252885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41426567190654369048030773 3883740674123847098252885)
              ·
                refine ⟨45512586024888833182651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3883740674123847098252885 45512586024888833182651)
                ·
                  rfl

theorem cell23_2393157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 8].length) (baseStart_2393157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393157 prefixEnd_2393157 := by exact prefixLift 2393157
  have htrace : WordTrace (prefixWord ++ tailWord_2393157) baseStart_2393157 baseEnd_2393157 := by
    simpa [prefixWord, tailWord_2393157, baseEnd_2393157] using wordTrace_append hprefix tailTrace_2393157
  have hstable : (prefixWord ++ tailWord_2393157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393157).length < 2 ^ (prefixWord ++ tailWord_2393157).sum := by decide
  have hdescent : baseEnd_2393157 < baseStart_2393157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393182 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2393182 : Nat := 118140960795 + 2393182 * 2 ^ 59
def prefixEnd_2393182 : Nat := 4983230072969 + 3 ^ 40 * 2393182 * 2
def baseEnd_2393182 : Nat := 409617553229453632706321

theorem tailTrace_2393182 : CollatzResearch.WordTrace tailWord_2393182 prefixEnd_2393182 409617553229453632706321 := by
  unfold tailWord_2393182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10910814801989726473826725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58191012277278541193742533 10910814801989726473826725)
  ·
    refine ⟨2045777775373073713842511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10910814801989726473826725 2045777775373073713842511)
    ·
      refine ⟨3068666663059610570763767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2045777775373073713842511 3068666663059610570763767)
      ·
        refine ⟨4602999994589415856145651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3068666663059610570763767 4602999994589415856145651)
        ·
          refine ⟨6904499991884123784218477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4602999994589415856145651 6904499991884123784218477)
          ·
            refine ⟨2589187496956546419081929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6904499991884123784218477 2589187496956546419081929)
            ·
              refine ⟨1941890622717409814311447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2589187496956546419081929 1941890622717409814311447)
              ·
                refine ⟨2912835934076114721467171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941890622717409814311447 2912835934076114721467171)
                ·
                  refine ⟨4369253901114172082200757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912835934076114721467171 4369253901114172082200757)
                  ·
                    refine ⟨409617553229453632706321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4369253901114172082200757 409617553229453632706321)
                    ·
                      rfl

theorem cell23_2393182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2393182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393182 prefixEnd_2393182 := by exact prefixLift 2393182
  have htrace : WordTrace (prefixWord ++ tailWord_2393182) baseStart_2393182 baseEnd_2393182 := by
    simpa [prefixWord, tailWord_2393182, baseEnd_2393182] using wordTrace_append hprefix tailTrace_2393182
  have hstable : (prefixWord ++ tailWord_2393182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393182).length < 2 ^ (prefixWord ++ tailWord_2393182).sum := by decide
  have hdescent : baseEnd_2393182 < baseStart_2393182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393184 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 3]
def baseStart_2393184 : Nat := 118140960795 + 2393184 * 2 ^ 59
def prefixEnd_2393184 : Nat := 4983230072969 + 3 ^ 40 * 2393184 * 2
def baseEnd_2393184 : Nat := 1228853686649669890293953

theorem tailTrace_2393184 : CollatzResearch.WordTrace tailWord_2393184 prefixEnd_2393184 1228853686649669890293953 := by
  unfold tailWord_2393184
  simp only [CollatzResearch.WordTrace]
  refine ⟨43643295680955283066093303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58191060907940377421457737 43643295680955283066093303)
  ·
    refine ⟨65464943521432924599139955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43643295680955283066093303 65464943521432924599139955)
    ·
      refine ⟨98197415282149386898709933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65464943521432924599139955 98197415282149386898709933)
      ·
        refine ⟨36824030730806020087016225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98197415282149386898709933 36824030730806020087016225)
        ·
          refine ⟨27618023048104515065262169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36824030730806020087016225 27618023048104515065262169)
          ·
            refine ⟨20713517286078386298946627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27618023048104515065262169 20713517286078386298946627)
            ·
              refine ⟨31070275929117579448419941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20713517286078386298946627 31070275929117579448419941)
              ·
                refine ⟨5825676736709546146578739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31070275929117579448419941 5825676736709546146578739)
                ·
                  refine ⟨8738515105064319219868109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5825676736709546146578739 8738515105064319219868109)
                  ·
                    refine ⟨3276943164399119707450541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8738515105064319219868109 3276943164399119707450541)
                    ·
                      refine ⟨1228853686649669890293953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3276943164399119707450541 1228853686649669890293953)
                      ·
                        rfl

theorem cell23_2393184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_2393184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393184 prefixEnd_2393184 := by exact prefixLift 2393184
  have htrace : WordTrace (prefixWord ++ tailWord_2393184) baseStart_2393184 baseEnd_2393184 := by
    simpa [prefixWord, tailWord_2393184, baseEnd_2393184] using wordTrace_append hprefix tailTrace_2393184
  have hstable : (prefixWord ++ tailWord_2393184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393184).length < 2 ^ (prefixWord ++ tailWord_2393184).sum := by decide
  have hdescent : baseEnd_2393184 < baseStart_2393184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393201 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 2, 1, 3]
def baseStart_2393201 : Nat := 118140960795 + 2393201 * 2 ^ 59
def prefixEnd_2393201 : Nat := 4983230072969 + 3 ^ 40 * 2393201 * 2
def baseEnd_2393201 : Nat := 1228862415820796323781375

theorem tailTrace_2393201 : CollatzResearch.WordTrace tailWord_2393201 prefixEnd_2393201 1228862415820796323781375 := by
  unfold tailWord_2393201
  simp only [CollatzResearch.WordTrace]
  refine ⟨87287211402848978035555457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58191474268565985357036971 87287211402848978035555457)
  ·
    refine ⟨65465408552136733526666593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87287211402848978035555457 65465408552136733526666593)
    ·
      refine ⟨49099056414102550144999945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65465408552136733526666593 49099056414102550144999945)
      ·
        refine ⟨36824292310576912608749959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49099056414102550144999945 36824292310576912608749959)
        ·
          refine ⟨55236438465865368913124939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36824292310576912608749959 55236438465865368913124939)
          ·
            refine ⟨82854657698798053369687409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55236438465865368913124939 82854657698798053369687409)
            ·
              refine ⟨62140993274098540027265557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82854657698798053369687409 62140993274098540027265557)
              ·
                refine ⟨2912859059723369063778073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62140993274098540027265557 2912859059723369063778073)
                ·
                  refine ⟨2184644294792526797833555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2912859059723369063778073 2184644294792526797833555)
                  ·
                    refine ⟨3276966442188790196750333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2184644294792526797833555 3276966442188790196750333)
                    ·
                      refine ⟨1228862415820796323781375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3276966442188790196750333 1228862415820796323781375)
                      ·
                        rfl

theorem cell23_2393201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_2393201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393201 prefixEnd_2393201 := by exact prefixLift 2393201
  have htrace : WordTrace (prefixWord ++ tailWord_2393201) baseStart_2393201 baseEnd_2393201 := by
    simpa [prefixWord, tailWord_2393201, baseEnd_2393201] using wordTrace_append hprefix tailTrace_2393201
  have hstable : (prefixWord ++ tailWord_2393201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393201).length < 2 ^ (prefixWord ++ tailWord_2393201).sum := by decide
  have hdescent : baseEnd_2393201 < baseStart_2393201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393227 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 5]
def baseStart_2393227 : Nat := 118140960795 + 2393227 * 2 ^ 59
def prefixEnd_2393227 : Nat := 4983230072969 + 3 ^ 40 * 2393227 * 2
def baseEnd_2393227 : Nat := 1228875766317813222056255

theorem tailTrace_2393227 : CollatzResearch.WordTrace tailWord_2393227 prefixEnd_2393227 1228875766317813222056255 := by
  unfold tailWord_2393227
  simp only [CollatzResearch.WordTrace]
  refine ⟨87288159700754784476001935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58192106467169856317334623 87288159700754784476001935)
  ·
    refine ⟨130932239551132176714002903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87288159700754784476001935 130932239551132176714002903)
    ·
      refine ⟨196398359326698265071004355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130932239551132176714002903 196398359326698265071004355)
      ·
        refine ⟨294597538990047397606506533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196398359326698265071004355 294597538990047397606506533)
        ·
          refine ⟨55237038560633887051219975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 294597538990047397606506533 55237038560633887051219975)
          ·
            refine ⟨82855557840950830576829963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55237038560633887051219975 82855557840950830576829963)
            ·
              refine ⟨124283336761426245865244945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82855557840950830576829963 124283336761426245865244945)
              ·
                refine ⟨93212502571069684398933709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124283336761426245865244945 93212502571069684398933709)
                ·
                  refine ⟨34954688464151131649600141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93212502571069684398933709 34954688464151131649600141)
                  ·
                    refine ⟨13108008174056674368600053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34954688464151131649600141 13108008174056674368600053)
                    ·
                      refine ⟨1228875766317813222056255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13108008174056674368600053 1228875766317813222056255)
                      ·
                        rfl

theorem cell23_2393227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_2393227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393227 prefixEnd_2393227 := by exact prefixLift 2393227
  have htrace : WordTrace (prefixWord ++ tailWord_2393227) baseStart_2393227 baseEnd_2393227 := by
    simpa [prefixWord, tailWord_2393227, baseEnd_2393227] using wordTrace_append hprefix tailTrace_2393227
  have hstable : (prefixWord ++ tailWord_2393227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393227).length < 2 ^ (prefixWord ++ tailWord_2393227).sum := by decide
  have hdescent : baseEnd_2393227 < baseStart_2393227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393244 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2393244 : Nat := 118140960795 + 2393244 * 2 ^ 59
def prefixEnd_2393244 : Nat := 4983230072969 + 3 ^ 40 * 2393244 * 2
def baseEnd_2393244 : Nat := 1228884495488939655543677

theorem tailTrace_2393244 : CollatzResearch.WordTrace tailWord_2393244 prefixEnd_2393244 1228884495488939655543677 := by
  unfold tailWord_2393244
  simp only [CollatzResearch.WordTrace]
  refine ⟨43644389870846598189685393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58192519827795464252913857 43644389870846598189685393)
  ·
    refine ⟨32733292403134948642264045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43644389870846598189685393 32733292403134948642264045)
    ·
      refine ⟨12274984651175605740849017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32733292403134948642264045 12274984651175605740849017)
      ·
        refine ⟨9206238488381704305636763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12274984651175605740849017 9206238488381704305636763)
        ·
          refine ⟨13809357732572556458455145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9206238488381704305636763 13809357732572556458455145)
          ·
            refine ⟨10357018299429417343841359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13809357732572556458455145 10357018299429417343841359)
            ·
              refine ⟨15535527449144126015762039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10357018299429417343841359 15535527449144126015762039)
              ·
                refine ⟨23303291173716189023643059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15535527449144126015762039 23303291173716189023643059)
                ·
                  refine ⟨34954936760574283535464589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23303291173716189023643059 34954936760574283535464589)
                  ·
                    refine ⟨13108101285215356325799221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34954936760574283535464589 13108101285215356325799221)
                    ·
                      refine ⟨1228884495488939655543677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13108101285215356325799221 1228884495488939655543677)
                      ·
                        rfl

theorem cell23_2393244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2393244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393244 prefixEnd_2393244 := by exact prefixLift 2393244
  have htrace : WordTrace (prefixWord ++ tailWord_2393244) baseStart_2393244 baseEnd_2393244 := by
    simpa [prefixWord, tailWord_2393244, baseEnd_2393244] using wordTrace_append hprefix tailTrace_2393244
  have hstable : (prefixWord ++ tailWord_2393244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393244).length < 2 ^ (prefixWord ++ tailWord_2393244).sum := by decide
  have hdescent : baseEnd_2393244 < baseStart_2393244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393274 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3]
def baseStart_2393274 : Nat := 118140960795 + 2393274 * 2 ^ 59
def prefixEnd_2393274 : Nat := 4983230072969 + 3 ^ 40 * 2393274 * 2
def baseEnd_2393274 : Nat := 1228899899908574538168539

theorem tailTrace_2393274 : CollatzResearch.WordTrace tailWord_2393274 prefixEnd_2393274 1228899899908574538168539 := by
  unfold tailWord_2393274
  simp only [CollatzResearch.WordTrace]
  refine ⟨21822468482896127875740719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58193249287723007668641917 21822468482896127875740719)
  ·
    refine ⟨32733702724344191813611079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21822468482896127875740719 32733702724344191813611079)
    ·
      refine ⟨49100554086516287720416619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32733702724344191813611079 49100554086516287720416619)
      ·
        refine ⟨73650831129774431580624929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49100554086516287720416619 73650831129774431580624929)
        ·
          refine ⟨55238123347330823685468697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73650831129774431580624929 55238123347330823685468697)
          ·
            refine ⟨41428592510498117764101523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55238123347330823685468697 41428592510498117764101523)
            ·
              refine ⟨62142888765747176646152285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41428592510498117764101523 62142888765747176646152285)
              ·
                refine ⟨23303583287155191242307107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62142888765747176646152285 23303583287155191242307107)
                ·
                  refine ⟨34955374930732786863460661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23303583287155191242307107 34955374930732786863460661)
                  ·
                    refine ⟨3277066399756198768449437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34955374930732786863460661 3277066399756198768449437)
                    ·
                      refine ⟨1228899899908574538168539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3277066399756198768449437 1228899899908574538168539)
                      ·
                        rfl

theorem cell23_2393274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_2393274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393274 prefixEnd_2393274 := by exact prefixLift 2393274
  have htrace : WordTrace (prefixWord ++ tailWord_2393274) baseStart_2393274 baseEnd_2393274 := by
    simpa [prefixWord, tailWord_2393274, baseEnd_2393274] using wordTrace_append hprefix tailTrace_2393274
  have hstable : (prefixWord ++ tailWord_2393274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393274).length < 2 ^ (prefixWord ++ tailWord_2393274).sum := by decide
  have hdescent : baseEnd_2393274 < baseStart_2393274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393331 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 1, 6, 2]
def baseStart_2393331 : Nat := 118140960795 + 2393331 * 2 ^ 59
def prefixEnd_2393331 : Nat := 4983230072969 + 3 ^ 40 * 2393331 * 2
def baseEnd_2393331 : Nat := 1228929168305880815155777

theorem tailTrace_2393331 : CollatzResearch.WordTrace tailWord_2393331 prefixEnd_2393331 1228929168305880815155777 := by
  unfold tailWord_2393331
  simp only [CollatzResearch.WordTrace]
  refine ⟨87291952892378010237787847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58194635261585340158525231 87291952892378010237787847)
  ·
    refine ⟨130937929338567015356681771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87291952892378010237787847 130937929338567015356681771)
    ·
      refine ⟨196406894007850523035022657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130937929338567015356681771 196406894007850523035022657)
      ·
        refine ⟨147305170505887892276266993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196406894007850523035022657 147305170505887892276266993)
        ·
          refine ⟨110478877879415919207200245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147305170505887892276266993 110478877879415919207200245)
          ·
            refine ⟨10357394801195242425675023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110478877879415919207200245 10357394801195242425675023)
            ·
              refine ⟨15536092201792863638512535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10357394801195242425675023 15536092201792863638512535)
              ·
                refine ⟨23304138302689295457768803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15536092201792863638512535 23304138302689295457768803)
                ·
                  refine ⟨34956207454033943186653205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23304138302689295457768803 34956207454033943186653205)
                  ·
                    refine ⟨1638572224407841086874369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34956207454033943186653205 1638572224407841086874369)
                    ·
                      refine ⟨1228929168305880815155777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638572224407841086874369 1228929168305880815155777)
                      ·
                        rfl

theorem cell23_2393331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 6, 2].length) (baseStart_2393331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393331 prefixEnd_2393331 := by exact prefixLift 2393331
  have htrace : WordTrace (prefixWord ++ tailWord_2393331) baseStart_2393331 baseEnd_2393331 := by
    simpa [prefixWord, tailWord_2393331, baseEnd_2393331] using wordTrace_append hprefix tailTrace_2393331
  have hstable : (prefixWord ++ tailWord_2393331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393331).length < 2 ^ (prefixWord ++ tailWord_2393331).sum := by decide
  have hdescent : baseEnd_2393331 < baseStart_2393331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393348 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_2393348 : Nat := 118140960795 + 2393348 * 2 ^ 59
def prefixEnd_2393348 : Nat := 4983230072969 + 3 ^ 40 * 2393348 * 2
def baseEnd_2393348 : Nat := 1228937897477007248643199

theorem tailTrace_2393348 : CollatzResearch.WordTrace tailWord_2393348 prefixEnd_2393348 1228937897477007248643199 := by
  unfold tailWord_2393348
  simp only [CollatzResearch.WordTrace]
  refine ⟨43646286466658211070578349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58195048622210948094104465 43646286466658211070578349)
  ·
    refine ⟨16367357424996829151466881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43646286466658211070578349 16367357424996829151466881)
    ·
      refine ⟨12275518068747621863600161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16367357424996829151466881 12275518068747621863600161)
      ·
        refine ⟨9206638551560716397700121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12275518068747621863600161 9206638551560716397700121)
        ·
          refine ⟨6904978913670537298275091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9206638551560716397700121 6904978913670537298275091)
          ·
            refine ⟨10357468370505805947412637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6904978913670537298275091 10357468370505805947412637)
            ·
              refine ⟨3884050638939677230279739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10357468370505805947412637 3884050638939677230279739)
              ·
                refine ⟨5826075958409515845419609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884050638939677230279739 5826075958409515845419609)
                ·
                  refine ⟨4369556968807136884064707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5826075958409515845419609 4369556968807136884064707)
                  ·
                    refine ⟨6554335453210705326097061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4369556968807136884064707 6554335453210705326097061)
                    ·
                      refine ⟨1228937897477007248643199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6554335453210705326097061 1228937897477007248643199)
                      ·
                        rfl

theorem cell23_2393348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_2393348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393348 prefixEnd_2393348 := by exact prefixLift 2393348
  have htrace : WordTrace (prefixWord ++ tailWord_2393348) baseStart_2393348 baseEnd_2393348 := by
    simpa [prefixWord, tailWord_2393348, baseEnd_2393348] using wordTrace_append hprefix tailTrace_2393348
  have hstable : (prefixWord ++ tailWord_2393348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393348).length < 2 ^ (prefixWord ++ tailWord_2393348).sum := by decide
  have hdescent : baseEnd_2393348 < baseStart_2393348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393354 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 8]
def baseStart_2393354 : Nat := 118140960795 + 2393354 * 2 ^ 59
def prefixEnd_2393354 : Nat := 4983230072969 + 3 ^ 40 * 2393354 * 2
def baseEnd_2393354 : Nat := 136548997595659358352019

theorem tailTrace_2393354 : CollatzResearch.WordTrace tailWord_2393354 prefixEnd_2393354 136548997595659358352019 := by
  unfold tailWord_2393354
  simp only [CollatzResearch.WordTrace]
  refine ⟨21823197942823671291468779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58195194514196456777250077 21823197942823671291468779)
  ·
    refine ⟨32734796914235506937203169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21823197942823671291468779 32734796914235506937203169)
    ·
      refine ⟨24551097685676630202902377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32734796914235506937203169 24551097685676630202902377)
      ·
        refine ⟨18413323264257472652176783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24551097685676630202902377 18413323264257472652176783)
        ·
          refine ⟨27619984896386208978265175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18413323264257472652176783 27619984896386208978265175)
          ·
            refine ⟨41429977344579313467397763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27619984896386208978265175 41429977344579313467397763)
            ·
              refine ⟨62144966016868970201096645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41429977344579313467397763 62144966016868970201096645)
              ·
                refine ⟨11652181128162931912705621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62144966016868970201096645 11652181128162931912705621)
                ·
                  refine ⟨136548997595659358352019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11652181128162931912705621 136548997595659358352019)
                  ·
                    rfl

theorem cell23_2393354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_2393354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393354 prefixEnd_2393354 := by exact prefixLift 2393354
  have htrace : WordTrace (prefixWord ++ tailWord_2393354) baseStart_2393354 baseEnd_2393354 := by
    simpa [prefixWord, tailWord_2393354, baseEnd_2393354] using wordTrace_append hprefix tailTrace_2393354
  have hstable : (prefixWord ++ tailWord_2393354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393354).length < 2 ^ (prefixWord ++ tailWord_2393354).sum := by decide
  have hdescent : baseEnd_2393354 < baseStart_2393354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393408 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 2, 3, 2]
def baseStart_2393408 : Nat := 118140960795 + 2393408 * 2 ^ 59
def prefixEnd_2393408 : Nat := 4983230072969 + 3 ^ 40 * 2393408 * 2
def baseEnd_2393408 : Nat := 1228968706316277013892923

theorem tailTrace_2393408 : CollatzResearch.WordTrace tailWord_2393408 prefixEnd_2393408 1228968706316277013892923 := by
  unfold tailWord_2393408
  simp only [CollatzResearch.WordTrace]
  refine ⟨43647380656549526194170439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58196507542066034925560585 43647380656549526194170439)
  ·
    refine ⟨65471070984824289291255659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43647380656549526194170439 65471070984824289291255659)
    ·
      refine ⟨98206606477236433936883489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65471070984824289291255659 98206606477236433936883489)
      ·
        refine ⟨73654954857927325452662617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98206606477236433936883489 73654954857927325452662617)
        ·
          refine ⟨55241216143445494089496963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73654954857927325452662617 55241216143445494089496963)
          ·
            refine ⟨82861824215168241134245445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55241216143445494089496963 82861824215168241134245445)
            ·
              refine ⟨15536592040344045212671021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82861824215168241134245445 15536592040344045212671021)
              ·
                refine ⟨5826222015129016954751633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15536592040344045212671021 5826222015129016954751633)
                ·
                  refine ⟨4369666511346762716063725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5826222015129016954751633 4369666511346762716063725)
                  ·
                    refine ⟨1638624941755036018523897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4369666511346762716063725 1638624941755036018523897)
                    ·
                      refine ⟨1228968706316277013892923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638624941755036018523897 1228968706316277013892923)
                      ·
                        rfl

theorem cell23_2393408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 3, 2].length) (baseStart_2393408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393408 prefixEnd_2393408 := by exact prefixLift 2393408
  have htrace : WordTrace (prefixWord ++ tailWord_2393408) baseStart_2393408 baseEnd_2393408 := by
    simpa [prefixWord, tailWord_2393408, baseEnd_2393408] using wordTrace_append hprefix tailTrace_2393408
  have hstable : (prefixWord ++ tailWord_2393408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393408).length < 2 ^ (prefixWord ++ tailWord_2393408).sum := by decide
  have hdescent : baseEnd_2393408 < baseStart_2393408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393432 : List Nat := [2, 1, 2, 2, 1, 1, 7, 2, 1, 1, 3]
def baseStart_2393432 : Nat := 118140960795 + 2393432 * 2 ^ 59
def prefixEnd_2393432 : Nat := 4983230072969 + 3 ^ 40 * 2393432 * 2
def baseEnd_2393432 : Nat := 1228981029851984919992813

theorem tailTrace_2393432 : CollatzResearch.WordTrace tailWord_2393432 prefixEnd_2393432 1228981029851984919992813 := by
  unfold tailWord_2393432
  simp only [CollatzResearch.WordTrace]
  refine ⟨43647818332506052243607275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58197091110008069658143033 43647818332506052243607275)
  ·
    refine ⟨65471727498759078365410913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43647818332506052243607275 65471727498759078365410913)
    ·
      refine ⟨49103795624069308774058185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65471727498759078365410913 49103795624069308774058185)
      ·
        refine ⟨36827846718051981580543639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49103795624069308774058185 36827846718051981580543639)
        ·
          refine ⟨55241770077077972370815459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36827846718051981580543639 55241770077077972370815459)
          ·
            refine ⟨82862655115616958556223189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55241770077077972370815459 82862655115616958556223189)
            ·
              refine ⟨1942093479272272466161481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 82862655115616958556223189 1942093479272272466161481)
              ·
                refine ⟨1456570109454204349621111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942093479272272466161481 1456570109454204349621111)
                ·
                  refine ⟨2184855164181306524431667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456570109454204349621111 2184855164181306524431667)
                  ·
                    refine ⟨3277282746271959786647501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2184855164181306524431667 3277282746271959786647501)
                    ·
                      refine ⟨1228981029851984919992813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3277282746271959786647501 1228981029851984919992813)
                      ·
                        rfl

theorem cell23_2393432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_2393432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393432 prefixEnd_2393432 := by exact prefixLift 2393432
  have htrace : WordTrace (prefixWord ++ tailWord_2393432) baseStart_2393432 baseEnd_2393432 := by
    simpa [prefixWord, tailWord_2393432, baseEnd_2393432] using wordTrace_append hprefix tailTrace_2393432
  have hstable : (prefixWord ++ tailWord_2393432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393432).length < 2 ^ (prefixWord ++ tailWord_2393432).sum := by decide
  have hdescent : baseEnd_2393432 < baseStart_2393432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393458 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_2393458 : Nat := 118140960795 + 2393458 * 2 ^ 59
def prefixEnd_2393458 : Nat := 4983230072969 + 3 ^ 40 * 2393458 * 2
def baseEnd_2393458 : Nat := 1228994380349001818267693

theorem tailTrace_2393458 : CollatzResearch.WordTrace tailWord_2393458 prefixEnd_2393458 1228994380349001818267693 := by
  unfold tailWord_2393458
  simp only [CollatzResearch.WordTrace]
  refine ⟨21824146240729477731915257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58197723308611940618440685 21824146240729477731915257)
  ·
    refine ⟨16368109680547108298936443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21824146240729477731915257 16368109680547108298936443)
    ·
      refine ⟨24552164520820662448404665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16368109680547108298936443 24552164520820662448404665)
      ·
        refine ⟨18414123390615496836303499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24552164520820662448404665 18414123390615496836303499)
        ·
          refine ⟨27621185085923245254455249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18414123390615496836303499 27621185085923245254455249)
          ·
            refine ⟨20715888814442433940841437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27621185085923245254455249 20715888814442433940841437)
            ·
              refine ⟨7768458305415912727815539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20715888814442433940841437 7768458305415912727815539)
              ·
                refine ⟨11652687458123869091723309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7768458305415912727815539 11652687458123869091723309)
                ·
                  refine ⟨4369757796796450909396241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11652687458123869091723309 4369757796796450909396241)
                  ·
                    refine ⟨3277318347597338182047181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4369757796796450909396241 3277318347597338182047181)
                    ·
                      refine ⟨1228994380349001818267693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3277318347597338182047181 1228994380349001818267693)
                      ·
                        rfl

theorem cell23_2393458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_2393458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393458 prefixEnd_2393458 := by exact prefixLift 2393458
  have htrace : WordTrace (prefixWord ++ tailWord_2393458) baseStart_2393458 baseEnd_2393458 := by
    simpa [prefixWord, tailWord_2393458, baseEnd_2393458] using wordTrace_append hprefix tailTrace_2393458
  have hstable : (prefixWord ++ tailWord_2393458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393458).length < 2 ^ (prefixWord ++ tailWord_2393458).sum := by decide
  have hdescent : baseEnd_2393458 < baseStart_2393458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393502 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2393502 : Nat := 118140960795 + 2393502 * 2 ^ 59
def prefixEnd_2393502 : Nat := 4983230072969 + 3 ^ 40 * 2393502 * 2
def baseEnd_2393502 : Nat := 1229016973497799646117491

theorem tailTrace_2393502 : CollatzResearch.WordTrace tailWord_2393502 prefixEnd_2393502 1229016973497799646117491 := by
  unfold tailWord_2393502
  simp only [CollatzResearch.WordTrace]
  refine ⟨10912273721844813305282845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58198793183172337628175173 10912273721844813305282845)
  ·
    refine ⟨4092102645691804989481067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10912273721844813305282845 4092102645691804989481067)
    ·
      refine ⟨6138153968537707484221601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4092102645691804989481067 6138153968537707484221601)
      ·
        refine ⟨4603615476403280613166201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6138153968537707484221601 4603615476403280613166201)
        ·
          refine ⟨3452711607302460459874651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4603615476403280613166201 3452711607302460459874651)
          ·
            refine ⟨5179067410953690689811977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452711607302460459874651 5179067410953690689811977)
            ·
              refine ⟨3884300558215268017358983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5179067410953690689811977 3884300558215268017358983)
              ·
                refine ⟨5826450837322902026038475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884300558215268017358983 5826450837322902026038475)
                ·
                  refine ⟨8739676255984353039057713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826450837322902026038475 8739676255984353039057713)
                  ·
                    refine ⟨6554757191988264779293285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8739676255984353039057713 6554757191988264779293285)
                    ·
                      refine ⟨1229016973497799646117491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6554757191988264779293285 1229016973497799646117491)
                      ·
                        rfl

theorem cell23_2393502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2393502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393502 prefixEnd_2393502 := by exact prefixLift 2393502
  have htrace : WordTrace (prefixWord ++ tailWord_2393502) baseStart_2393502 baseEnd_2393502 := by
    simpa [prefixWord, tailWord_2393502, baseEnd_2393502] using wordTrace_append hprefix tailTrace_2393502
  have hstable : (prefixWord ++ tailWord_2393502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393502).length < 2 ^ (prefixWord ++ tailWord_2393502).sum := by decide
  have hdescent : baseEnd_2393502 < baseStart_2393502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393521 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 1, 8]
def baseStart_2393521 : Nat := 118140960795 + 2393521 * 2 ^ 59
def prefixEnd_2393521 : Nat := 4983230072969 + 3 ^ 40 * 2393521 * 2
def baseEnd_2393521 : Nat := 409675576543411690593301

theorem tailTrace_2393521 : CollatzResearch.WordTrace tailWord_2393521 prefixEnd_2393521 409675576543411690593301 := by
  unfold tailWord_2393521
  simp only [CollatzResearch.WordTrace]
  refine ⟨87298882761689672687204417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58199255174459781791469611 87298882761689672687204417)
  ·
    refine ⟨65474162071267254515403313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87298882761689672687204417 65474162071267254515403313)
    ·
      refine ⟨49105621553450440886552485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65474162071267254515403313 49105621553450440886552485)
      ·
        refine ⟨9207304041271957666228591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49105621553450440886552485 9207304041271957666228591)
        ·
          refine ⟨13810956061907936499342887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9207304041271957666228591 13810956061907936499342887)
          ·
            refine ⟨20716434092861904749014331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13810956061907936499342887 20716434092861904749014331)
            ·
              refine ⟨31074651139292857123521497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20716434092861904749014331 31074651139292857123521497)
              ·
                refine ⟨23305988354469642842641123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31074651139292857123521497 23305988354469642842641123)
                ·
                  refine ⟨34958982531704464263961685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23305988354469642842641123 34958982531704464263961685)
                  ·
                    refine ⟨409675576543411690593301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34958982531704464263961685 409675576543411690593301)
                    ·
                      rfl

theorem cell23_2393521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_2393521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393521 prefixEnd_2393521 := by exact prefixLift 2393521
  have htrace : WordTrace (prefixWord ++ tailWord_2393521) baseStart_2393521 baseEnd_2393521 := by
    simpa [prefixWord, tailWord_2393521, baseEnd_2393521] using wordTrace_append hprefix tailTrace_2393521
  have hstable : (prefixWord ++ tailWord_2393521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393521).length < 2 ^ (prefixWord ++ tailWord_2393521).sum := by decide
  have hdescent : baseEnd_2393521 < baseStart_2393521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393551 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 7]
def baseStart_2393551 : Nat := 118140960795 + 2393551 * 2 ^ 59
def prefixEnd_2393551 : Nat := 4983230072969 + 3 ^ 40 * 2393551 * 2
def baseEnd_2393551 : Nat := 136560237116652217156085

theorem tailTrace_2393551 : CollatzResearch.WordTrace tailWord_2393551 prefixEnd_2393551 136560237116652217156085 := by
  unfold tailWord_2393551
  simp only [CollatzResearch.WordTrace]
  refine ⟨87299976951580987810796507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58199984634387325207197671 87299976951580987810796507)
  ·
    refine ⟨130949965427371481716194761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87299976951580987810796507 130949965427371481716194761)
    ·
      refine ⟨98212474070528611287146071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130949965427371481716194761 98212474070528611287146071)
      ·
        refine ⟨147318711105792916930719107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98212474070528611287146071 147318711105792916930719107)
        ·
          refine ⟨220978066658689375396078661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147318711105792916930719107 220978066658689375396078661)
          ·
            refine ⟨41433387498504257886764749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220978066658689375396078661 41433387498504257886764749)
            ·
              refine ⟨15537520311939096707536781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41433387498504257886764749 15537520311939096707536781)
              ·
                refine ⟨5826570116977161265326293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15537520311939096707536781 5826570116977161265326293)
                ·
                  refine ⟨136560237116652217156085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5826570116977161265326293 136560237116652217156085)
                  ·
                    rfl

theorem cell23_2393551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 7].length) (baseStart_2393551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393551 prefixEnd_2393551 := by exact prefixLift 2393551
  have htrace : WordTrace (prefixWord ++ tailWord_2393551) baseStart_2393551 baseEnd_2393551 := by
    simpa [prefixWord, tailWord_2393551, baseEnd_2393551] using wordTrace_append hprefix tailTrace_2393551
  have hstable : (prefixWord ++ tailWord_2393551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393551).length < 2 ^ (prefixWord ++ tailWord_2393551).sum := by decide
  have hdescent : baseEnd_2393551 < baseStart_2393551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393562 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2]
def baseStart_2393562 : Nat := 118140960795 + 2393562 * 2 ^ 59
def prefixEnd_2393562 : Nat := 4983230072969 + 3 ^ 40 * 2393562 * 2
def baseEnd_2393562 : Nat := 1229047782337069411367215

theorem tailTrace_2393562 : CollatzResearch.WordTrace tailWord_2393562 prefixEnd_2393562 1229047782337069411367215 := by
  unfold tailWord_2393562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21825094538635284172361735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58200252103027424459631293 21825094538635284172361735)
  ·
    refine ⟨32737641807952926258542603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21825094538635284172361735 32737641807952926258542603)
    ·
      refine ⟨49106462711929389387813905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32737641807952926258542603 49106462711929389387813905)
      ·
        refine ⟨36829847033947042040860429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49106462711929389387813905 36829847033947042040860429)
        ·
          refine ⟨13811192637730140765322661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36829847033947042040860429 13811192637730140765322661)
          ·
            refine ⟨2589598619574401393497999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13811192637730140765322661 2589598619574401393497999)
            ·
              refine ⟨3884397929361602090246999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589598619574401393497999 3884397929361602090246999)
              ·
                refine ⟨5826596894042403135370499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884397929361602090246999 5826596894042403135370499)
                ·
                  refine ⟨8739895341063604703055749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826596894042403135370499 8739895341063604703055749)
                  ·
                    refine ⟨1638730376449425881822953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8739895341063604703055749 1638730376449425881822953)
                    ·
                      refine ⟨1229047782337069411367215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638730376449425881822953 1229047782337069411367215)
                      ·
                        rfl

theorem cell23_2393562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_2393562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393562 prefixEnd_2393562 := by exact prefixLift 2393562
  have htrace : WordTrace (prefixWord ++ tailWord_2393562) baseStart_2393562 baseEnd_2393562 := by
    simpa [prefixWord, tailWord_2393562, baseEnd_2393562] using wordTrace_append hprefix tailTrace_2393562
  have hstable : (prefixWord ++ tailWord_2393562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393562).length < 2 ^ (prefixWord ++ tailWord_2393562).sum := by decide
  have hdescent : baseEnd_2393562 < baseStart_2393562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393585 : List Nat := [1, 2, 2, 2, 3, 2, 3, 3, 5]
def baseStart_2393585 : Nat := 118140960795 + 2393585 * 2 ^ 59
def prefixEnd_2393585 : Nat := 4983230072969 + 3 ^ 40 * 2393585 * 2
def baseEnd_2393585 : Nat := 136562176932458091264401

theorem tailTrace_2393585 : CollatzResearch.WordTrace tailWord_2393585 prefixEnd_2393585 136562176932458091264401 := by
  unfold tailWord_2393585
  simp only [CollatzResearch.WordTrace]
  refine ⟨87301217033457811617534209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58200811355638541078356139 87301217033457811617534209)
  ·
    refine ⟨65475912775093358713150657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87301217033457811617534209 65475912775093358713150657)
    ·
      refine ⟨49106934581320019034862993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65475912775093358713150657 49106934581320019034862993)
      ·
        refine ⟨36830200935990014276147245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49106934581320019034862993 36830200935990014276147245)
        ·
          refine ⟨13811325350996255353555217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36830200935990014276147245 13811325350996255353555217)
          ·
            refine ⟨10358494013247191515166413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13811325350996255353555217 10358494013247191515166413)
            ·
              refine ⟨3884435254967696818187405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10358494013247191515166413 3884435254967696818187405)
              ·
                refine ⟨1456663220612886306820277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3884435254967696818187405 1456663220612886306820277)
                ·
                  refine ⟨136562176932458091264401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1456663220612886306820277 136562176932458091264401)
                  ·
                    rfl

theorem cell23_2393585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 5].length) (baseStart_2393585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393585 prefixEnd_2393585 := by exact prefixLift 2393585
  have htrace : WordTrace (prefixWord ++ tailWord_2393585) baseStart_2393585 baseEnd_2393585 := by
    simpa [prefixWord, tailWord_2393585, baseEnd_2393585] using wordTrace_append hprefix tailTrace_2393585
  have hstable : (prefixWord ++ tailWord_2393585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393585).length < 2 ^ (prefixWord ++ tailWord_2393585).sum := by decide
  have hdescent : baseEnd_2393585 < baseStart_2393585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393602 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 7]
def baseStart_2393602 : Nat := 118140960795 + 2393602 * 2 ^ 59
def prefixEnd_2393602 : Nat := 4983230072969 + 3 ^ 40 * 2393602 * 2
def baseEnd_2393602 : Nat := 136563146840361028318559

theorem tailTrace_2393602 : CollatzResearch.WordTrace tailWord_2393602 prefixEnd_2393602 136563146840361028318559 := by
  unfold tailWord_2393602
  simp only [CollatzResearch.WordTrace]
  refine ⟨21825459268599055880225765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58201224716264149013935373 21825459268599055880225765)
  ·
    refine ⟨4092273612862322977542331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21825459268599055880225765 4092273612862322977542331)
    ·
      refine ⟨6138410419293484466313497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4092273612862322977542331 6138410419293484466313497)
      ·
        refine ⟨4603807814470113349735123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6138410419293484466313497 4603807814470113349735123)
        ·
          refine ⟨6905711721705170024602685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4603807814470113349735123 6905711721705170024602685)
          ·
            refine ⟨2589641895639438759226007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6905711721705170024602685 2589641895639438759226007)
            ·
              refine ⟨3884462843459158138839011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589641895639438759226007 3884462843459158138839011)
              ·
                refine ⟨5826694265188737208258517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884462843459158138839011 5826694265188737208258517)
                ·
                  refine ⟨136563146840361028318559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5826694265188737208258517 136563146840361028318559)
                  ·
                    rfl

theorem cell23_2393602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_2393602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393602 prefixEnd_2393602 := by exact prefixLift 2393602
  have htrace : WordTrace (prefixWord ++ tailWord_2393602) baseStart_2393602 baseEnd_2393602 := by
    simpa [prefixWord, tailWord_2393602, baseEnd_2393602] using wordTrace_append hprefix tailTrace_2393602
  have hstable : (prefixWord ++ tailWord_2393602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393602).length < 2 ^ (prefixWord ++ tailWord_2393602).sum := by decide
  have hdescent : baseEnd_2393602 < baseStart_2393602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393613 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_2393613 : Nat := 118140960795 + 2393613 * 2 ^ 59
def prefixEnd_2393613 : Nat := 4983230072969 + 3 ^ 40 * 2393613 * 2
def baseEnd_2393613 : Nat := 1229073969850448711829481

theorem tailTrace_2393613 : CollatzResearch.WordTrace tailWord_2393613 prefixEnd_2393613 1229073969850448711829481 := by
  unfold tailWord_2393613
  simp only [CollatzResearch.WordTrace]
  refine ⟨87302238277356372399553493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58201492184904248266368995 87302238277356372399553493)
  ·
    refine ⟨2046146209625539978114535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 87302238277356372399553493 2046146209625539978114535)
    ·
      refine ⟨3069219314438309967171803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2046146209625539978114535 3069219314438309967171803)
      ·
        refine ⟨4603828971657464950757705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3069219314438309967171803 4603828971657464950757705)
        ·
          refine ⟨3452871728743098713068279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4603828971657464950757705 3452871728743098713068279)
          ·
            refine ⟨5179307593114648069602419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452871728743098713068279 5179307593114648069602419)
            ·
              refine ⟨7768961389671972104403629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5179307593114648069602419 7768961389671972104403629)
              ·
                refine ⟨2913360521126989539151361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7768961389671972104403629 2913360521126989539151361)
                ·
                  refine ⟨2185020390845242154363521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2913360521126989539151361 2185020390845242154363521)
                  ·
                    refine ⟨1638765293133931615772641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2185020390845242154363521 1638765293133931615772641)
                    ·
                      refine ⟨1229073969850448711829481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638765293133931615772641 1229073969850448711829481)
                      ·
                        rfl

theorem cell23_2393613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_2393613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393613 prefixEnd_2393613 := by exact prefixLift 2393613
  have htrace : WordTrace (prefixWord ++ tailWord_2393613) baseStart_2393613 baseEnd_2393613 := by
    simpa [prefixWord, tailWord_2393613, baseEnd_2393613] using wordTrace_append hprefix tailTrace_2393613
  have hstable : (prefixWord ++ tailWord_2393613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393613).length < 2 ^ (prefixWord ++ tailWord_2393613).sum := by decide
  have hdescent : baseEnd_2393613 < baseStart_2393613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393655 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 3]
def baseStart_2393655 : Nat := 118140960795 + 2393655 * 2 ^ 59
def prefixEnd_2393655 : Nat := 4983230072969 + 3 ^ 40 * 2393655 * 2
def baseEnd_2393655 : Nat := 1229095536037937547504287

theorem tailTrace_2393655 : CollatzResearch.WordTrace tailWord_2393655 prefixEnd_2393655 1229095536037937547504287 := by
  unfold tailWord_2393655
  simp only [CollatzResearch.WordTrace]
  refine ⟨87303770143204213572582419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58202513428802809048388279 87303770143204213572582419)
  ·
    refine ⟨130955655214806320358873629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87303770143204213572582419 130955655214806320358873629)
    ·
      refine ⟨49108370705552370134577611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130955655214806320358873629 49108370705552370134577611)
      ·
        refine ⟨73662556058328555201866417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49108370705552370134577611 73662556058328555201866417)
        ·
          refine ⟨55246917043746416401399813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73662556058328555201866417 55246917043746416401399813)
          ·
            refine ⟨10358796945702453075262465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55246917043746416401399813 10358796945702453075262465)
            ·
              refine ⟨7769097709276839806446849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10358796945702453075262465 7769097709276839806446849)
              ·
                refine ⟨5826823281957629854835137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7769097709276839806446849 5826823281957629854835137)
                ·
                  refine ⟨4370117461468222391126353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5826823281957629854835137 4370117461468222391126353)
                  ·
                    refine ⟨3277588096101166793344765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4370117461468222391126353 3277588096101166793344765)
                    ·
                      refine ⟨1229095536037937547504287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3277588096101166793344765 1229095536037937547504287)
                      ·
                        rfl

theorem cell23_2393655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_2393655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393655 prefixEnd_2393655 := by exact prefixLift 2393655
  have htrace : WordTrace (prefixWord ++ tailWord_2393655) baseStart_2393655 baseEnd_2393655 := by
    simpa [prefixWord, tailWord_2393655, baseEnd_2393655] using wordTrace_append hprefix tailTrace_2393655
  have hstable : (prefixWord ++ tailWord_2393655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393655).length < 2 ^ (prefixWord ++ tailWord_2393655).sum := by decide
  have hdescent : baseEnd_2393655 < baseStart_2393655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393709 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 6]
def baseStart_2393709 : Nat := 118140960795 + 2393709 * 2 ^ 59
def prefixEnd_2393709 : Nat := 4983230072969 + 3 ^ 40 * 2393709 * 2
def baseEnd_2393709 : Nat := 136569251554808926247671

theorem tailTrace_2393709 : CollatzResearch.WordTrace tailWord_2393709 prefixEnd_2393709 136569251554808926247671 := by
  unfold tailWord_2393709
  simp only [CollatzResearch.WordTrace]
  refine ⟨87305739685008580795048181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58203826456672387196698787 87305739685008580795048181)
  ·
    refine ⟨8184913095469554449535767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87305739685008580795048181 8184913095469554449535767)
    ·
      refine ⟨12277369643204331674303651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8184913095469554449535767 12277369643204331674303651)
      ·
        refine ⟨18416054464806497511455477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12277369643204331674303651 18416054464806497511455477)
        ·
          refine ⟨1726505106075609141698951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18416054464806497511455477 1726505106075609141698951)
          ·
            refine ⟨2589757659113413712548427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726505106075609141698951 2589757659113413712548427)
            ·
              refine ⟨3884636488670120568822641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589757659113413712548427 3884636488670120568822641)
              ·
                refine ⟨2913477366502590426616981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3884636488670120568822641 2913477366502590426616981)
                ·
                  refine ⟨136569251554808926247671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2913477366502590426616981 136569251554808926247671)
                  ·
                    rfl

theorem cell23_2393709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_2393709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393709 prefixEnd_2393709 := by exact prefixLift 2393709
  have htrace : WordTrace (prefixWord ++ tailWord_2393709) baseStart_2393709 baseEnd_2393709 := by
    simpa [prefixWord, tailWord_2393709, baseEnd_2393709] using wordTrace_append hprefix tailTrace_2393709
  have hstable : (prefixWord ++ tailWord_2393709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393709).length < 2 ^ (prefixWord ++ tailWord_2393709).sum := by decide
  have hdescent : baseEnd_2393709 < baseStart_2393709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393735 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 1, 6]
def baseStart_2393735 : Nat := 118140960795 + 2393735 * 2 ^ 59
def prefixEnd_2393735 : Nat := 4983230072969 + 3 ^ 40 * 2393735 * 2
def baseEnd_2393735 : Nat := 409712204830099078167973

theorem tailTrace_2393735 : CollatzResearch.WordTrace tailWord_2393735 prefixEnd_2393735 409712204830099078167973 := by
  unfold tailWord_2393735
  simp only [CollatzResearch.WordTrace]
  refine ⟨87306687982914387235494659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58204458655276258156996439 87306687982914387235494659)
  ·
    refine ⟨130960031974371580853241989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87306687982914387235494659 130960031974371580853241989)
    ·
      refine ⟨24555005995194671409982873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130960031974371580853241989 24555005995194671409982873)
      ·
        refine ⟨18416254496396003557487155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24555005995194671409982873 18416254496396003557487155)
        ·
          refine ⟨27624381744594005336230733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18416254496396003557487155 27624381744594005336230733)
          ·
            refine ⟨10359143154222752001086525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27624381744594005336230733 10359143154222752001086525)
            ·
              refine ⟨3884678682833532000407447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10359143154222752001086525 3884678682833532000407447)
              ·
                refine ⟨5827018024250298000611171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884678682833532000407447 5827018024250298000611171)
                ·
                  refine ⟨8740527036375447000916757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5827018024250298000611171 8740527036375447000916757)
                  ·
                    refine ⟨409712204830099078167973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8740527036375447000916757 409712204830099078167973)
                    ·
                      rfl

theorem cell23_2393735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_2393735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393735 prefixEnd_2393735 := by exact prefixLift 2393735
  have htrace : WordTrace (prefixWord ++ tailWord_2393735) baseStart_2393735 baseEnd_2393735 := by
    simpa [prefixWord, tailWord_2393735, baseEnd_2393735] using wordTrace_append hprefix tailTrace_2393735
  have hstable : (prefixWord ++ tailWord_2393735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393735).length < 2 ^ (prefixWord ++ tailWord_2393735).sum := by decide
  have hdescent : baseEnd_2393735 < baseStart_2393735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393742 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_2393742 : Nat := 118140960795 + 2393742 * 2 ^ 59
def prefixEnd_2393742 : Nat := 4983230072969 + 3 ^ 40 * 2393742 * 2
def baseEnd_2393742 : Nat := 1229140208854878707116387

theorem tailTrace_2393742 : CollatzResearch.WordTrace tailWord_2393742 prefixEnd_2393742 1229140208854878707116387 := by
  unfold tailWord_2393742
  simp only [CollatzResearch.WordTrace]
  refine ⟨10913367911736128428874935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58204628862592684953999653 10913367911736128428874935)
  ·
    refine ⟨16370051867604192643312403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10913367911736128428874935 16370051867604192643312403)
    ·
      refine ⟨24555077801406288964968605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16370051867604192643312403 24555077801406288964968605)
      ·
        refine ⟨9208154175527358361863227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24555077801406288964968605 9208154175527358361863227)
        ·
          refine ⟨13812231263291037542794841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9208154175527358361863227 13812231263291037542794841)
          ·
            refine ⟨10359173447468278157096131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13812231263291037542794841 10359173447468278157096131)
            ·
              refine ⟨15538760171202417235644197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10359173447468278157096131 15538760171202417235644197)
              ·
                refine ⟨2913517532100453231683287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15538760171202417235644197 2913517532100453231683287)
                ·
                  refine ⟨4370276298150679847524931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2913517532100453231683287 4370276298150679847524931)
                  ·
                    refine ⟨6555414447226019771287397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4370276298150679847524931 6555414447226019771287397)
                    ·
                      refine ⟨1229140208854878707116387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6555414447226019771287397 1229140208854878707116387)
                      ·
                        rfl

theorem cell23_2393742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_2393742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393742 prefixEnd_2393742 := by exact prefixLift 2393742
  have htrace : WordTrace (prefixWord ++ tailWord_2393742) baseStart_2393742 baseEnd_2393742 := by
    simpa [prefixWord, tailWord_2393742, baseEnd_2393742] using wordTrace_append hprefix tailTrace_2393742
  have hstable : (prefixWord ++ tailWord_2393742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393742).length < 2 ^ (prefixWord ++ tailWord_2393742).sum := by decide
  have hdescent : baseEnd_2393742 < baseStart_2393742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393782 : List Nat := [5, 1, 3, 1, 1, 1, 1, 10]
def baseStart_2393782 : Nat := 118140960795 + 2393782 * 2 ^ 59
def prefixEnd_2393782 : Nat := 4983230072969 + 3 ^ 40 * 2393782 * 2
def baseEnd_2393782 : Nat := 45524472151150316689489

theorem tailTrace_2393782 : CollatzResearch.WordTrace tailWord_2393782 prefixEnd_2393782 45524472151150316689489 := by
  unfold tailWord_2393782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456775138359007141403475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58205601475829409508303733 5456775138359007141403475)
  ·
    refine ⟨8185162707538510712105213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5456775138359007141403475 8185162707538510712105213)
    ·
      refine ⟨3069436015326941517039455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8185162707538510712105213 3069436015326941517039455)
      ·
        refine ⟨4604154022990412275559183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3069436015326941517039455 4604154022990412275559183)
        ·
          refine ⟨6906231034485618413338775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4604154022990412275559183 6906231034485618413338775)
          ·
            refine ⟨10359346551728427620008163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6906231034485618413338775 10359346551728427620008163)
            ·
              refine ⟨15539019827592641430012245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10359346551728427620008163 15539019827592641430012245)
              ·
                refine ⟨45524472151150316689489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15539019827592641430012245 45524472151150316689489)
                ·
                  rfl

theorem cell23_2393782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_2393782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393782 prefixEnd_2393782 := by exact prefixLift 2393782
  have htrace : WordTrace (prefixWord ++ tailWord_2393782) baseStart_2393782 baseEnd_2393782 := by
    simpa [prefixWord, tailWord_2393782, baseEnd_2393782] using wordTrace_append hprefix tailTrace_2393782
  have hstable : (prefixWord ++ tailWord_2393782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393782).length < 2 ^ (prefixWord ++ tailWord_2393782).sum := by decide
  have hdescent : baseEnd_2393782 < baseStart_2393782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393808 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 3, 8]
def baseStart_2393808 : Nat := 118140960795 + 2393808 * 2 ^ 59
def prefixEnd_2393808 : Nat := 4983230072969 + 3 ^ 40 * 2393808 * 2
def baseEnd_2393808 : Nat := 409724699526025149630361

theorem tailTrace_2393808 : CollatzResearch.WordTrace tailWord_2393808 prefixEnd_2393808 409724699526025149630361 := by
  unfold tailWord_2393808
  simp only [CollatzResearch.WordTrace]
  refine ⟨43654675255824960351451039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58206233674433280468601385 43654675255824960351451039)
  ·
    refine ⟨65482012883737440527176559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43654675255824960351451039 65482012883737440527176559)
    ·
      refine ⟨98223019325606160790764839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65482012883737440527176559 98223019325606160790764839)
      ·
        refine ⟨147334528988409241186147259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98223019325606160790764839 147334528988409241186147259)
        ·
          refine ⟨221001793482613861779220889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147334528988409241186147259 221001793482613861779220889)
          ·
            refine ⟨165751345111960396334415667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221001793482613861779220889 165751345111960396334415667)
            ·
              refine ⟨248627017667940594501623501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165751345111960396334415667 248627017667940594501623501)
              ·
                refine ⟨93235131625477722938108813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248627017667940594501623501 93235131625477722938108813)
                ·
                  refine ⟨34963174359554146101790805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93235131625477722938108813 34963174359554146101790805)
                  ·
                    refine ⟨409724699526025149630361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34963174359554146101790805 409724699526025149630361)
                    ·
                      rfl

theorem cell23_2393808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_2393808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393808 prefixEnd_2393808 := by exact prefixLift 2393808
  have htrace : WordTrace (prefixWord ++ tailWord_2393808) baseStart_2393808 baseEnd_2393808 := by
    simpa [prefixWord, tailWord_2393808, baseEnd_2393808] using wordTrace_append hprefix tailTrace_2393808
  have hstable : (prefixWord ++ tailWord_2393808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393808).length < 2 ^ (prefixWord ++ tailWord_2393808).sum := by decide
  have hdescent : baseEnd_2393808 < baseStart_2393808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393827 : List Nat := [1, 1, 1, 7, 3, 1, 2, 2, 1, 2, 2]
def baseStart_2393827 : Nat := 118140960795 + 2393827 * 2 ^ 59
def prefixEnd_2393827 : Nat := 4983230072969 + 3 ^ 40 * 2393827 * 2
def baseEnd_2393827 : Nat := 1229183854710510874553497

theorem tailTrace_2393827 : CollatzResearch.WordTrace tailWord_2393827 prefixEnd_2393827 1229183854710510874553497 := by
  unfold tailWord_2393827
  simp only [CollatzResearch.WordTrace]
  refine ⟨87310043498581086947843735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58206695665720724631895823 87310043498581086947843735)
  ·
    refine ⟨130965065247871630421765603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87310043498581086947843735 130965065247871630421765603)
    ·
      refine ⟨196447597871807445632648405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130965065247871630421765603 196447597871807445632648405)
      ·
        refine ⟨4604240575120487007015197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 196447597871807445632648405 4604240575120487007015197)
        ·
          refine ⟨1726590215670182627630699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4604240575120487007015197 1726590215670182627630699)
          ·
            refine ⟨2589885323505273941446049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726590215670182627630699 2589885323505273941446049)
            ·
              refine ⟨1942413992628955456084537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2589885323505273941446049 1942413992628955456084537)
              ·
                refine ⟨1456810494471716592063403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942413992628955456084537 1456810494471716592063403)
                ·
                  refine ⟨2185215741707574888095105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456810494471716592063403 2185215741707574888095105)
                  ·
                    refine ⟨1638911806280681166071329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2185215741707574888095105 1638911806280681166071329)
                    ·
                      refine ⟨1229183854710510874553497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1638911806280681166071329 1229183854710510874553497)
                      ·
                        rfl

theorem cell23_2393827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_2393827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393827 prefixEnd_2393827 := by exact prefixLift 2393827
  have htrace : WordTrace (prefixWord ++ tailWord_2393827) baseStart_2393827 baseEnd_2393827 := by
    simpa [prefixWord, tailWord_2393827, baseEnd_2393827] using wordTrace_append hprefix tailTrace_2393827
  have hstable : (prefixWord ++ tailWord_2393827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393827).length < 2 ^ (prefixWord ++ tailWord_2393827).sum := by decide
  have hdescent : baseEnd_2393827 < baseStart_2393827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393835 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 3]
def baseStart_2393835 : Nat := 118140960795 + 2393835 * 2 ^ 59
def prefixEnd_2393835 : Nat := 4983230072969 + 3 ^ 40 * 2393835 * 2
def baseEnd_2393835 : Nat := 1229187962555746843253459

theorem tailTrace_2393835 : CollatzResearch.WordTrace tailWord_2393835 prefixEnd_2393835 1229187962555746843253459 := by
  unfold tailWord_2393835
  simp only [CollatzResearch.WordTrace]
  refine ⟨87310335282552104314134959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58206890188368069542756639 87310335282552104314134959)
  ·
    refine ⟨130965502923828156471202439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87310335282552104314134959 130965502923828156471202439)
    ·
      refine ⟨196448254385742234706803659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130965502923828156471202439 196448254385742234706803659)
      ·
        refine ⟨294672381578613352060205489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196448254385742234706803659 294672381578613352060205489)
        ·
          refine ⟨221004286183960014045154117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294672381578613352060205489 221004286183960014045154117)
          ·
            refine ⟨41438303659492502633466397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221004286183960014045154117 41438303659492502633466397)
            ·
              refine ⟨15539363872309688487549899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41438303659492502633466397 15539363872309688487549899)
              ·
                refine ⟨23309045808464532731324849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15539363872309688487549899 23309045808464532731324849)
                ·
                  refine ⟨17481784356348399548493637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23309045808464532731324849 17481784356348399548493637)
                  ·
                    refine ⟨3277834566815324915342557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17481784356348399548493637 3277834566815324915342557)
                    ·
                      refine ⟨1229187962555746843253459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3277834566815324915342557 1229187962555746843253459)
                      ·
                        rfl

theorem cell23_2393835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 3].length) (baseStart_2393835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393835 prefixEnd_2393835 := by exact prefixLift 2393835
  have htrace : WordTrace (prefixWord ++ tailWord_2393835) baseStart_2393835 baseEnd_2393835 := by
    simpa [prefixWord, tailWord_2393835, baseEnd_2393835] using wordTrace_append hprefix tailTrace_2393835
  have hstable : (prefixWord ++ tailWord_2393835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393835).length < 2 ^ (prefixWord ++ tailWord_2393835).sum := by decide
  have hdescent : baseEnd_2393835 < baseStart_2393835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393865 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 3, 5, 3]
def baseStart_2393865 : Nat := 118140960795 + 2393865 * 2 ^ 59
def prefixEnd_2393865 : Nat := 4983230072969 + 3 ^ 40 * 2393865 * 2
def baseEnd_2393865 : Nat := 1229203366975381725878321

theorem tailTrace_2393865 : CollatzResearch.WordTrace tailWord_2393865 prefixEnd_2393865 1229203366975381725878321 := by
  unfold tailWord_2393865
  simp only [CollatzResearch.WordTrace]
  refine ⟨87311429472443419437727049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58207619648295612958484699 87311429472443419437727049)
  ·
    refine ⟨65483572104332564578295287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87311429472443419437727049 65483572104332564578295287)
    ·
      refine ⟨98225358156498846867442931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65483572104332564578295287 98225358156498846867442931)
      ·
        refine ⟨147338037234748270301164397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98225358156498846867442931 147338037234748270301164397)
        ·
          refine ⟨55251763963030601362936649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147338037234748270301164397 55251763963030601362936649)
          ·
            refine ⟨41438822972272951022202487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55251763963030601362936649 41438822972272951022202487)
            ·
              refine ⟨62158234458409426533303731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41438822972272951022202487 62158234458409426533303731)
              ·
                refine ⟨93237351687614139799955597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62158234458409426533303731 93237351687614139799955597)
                ·
                  refine ⟨34964006882855302424983349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93237351687614139799955597 34964006882855302424983349)
                  ·
                    refine ⟨3277875645267684602342189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34964006882855302424983349 3277875645267684602342189)
                    ·
                      refine ⟨1229203366975381725878321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3277875645267684602342189 1229203366975381725878321)
                      ·
                        rfl

theorem cell23_2393865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5, 3].length) (baseStart_2393865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393865 prefixEnd_2393865 := by exact prefixLift 2393865
  have htrace : WordTrace (prefixWord ++ tailWord_2393865) baseStart_2393865 baseEnd_2393865 := by
    simpa [prefixWord, tailWord_2393865, baseEnd_2393865] using wordTrace_append hprefix tailTrace_2393865
  have hstable : (prefixWord ++ tailWord_2393865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393865).length < 2 ^ (prefixWord ++ tailWord_2393865).sum := by decide
  have hdescent : baseEnd_2393865 < baseStart_2393865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393882 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3]
def baseStart_2393882 : Nat := 118140960795 + 2393882 * 2 ^ 59
def prefixEnd_2393882 : Nat := 4983230072969 + 3 ^ 40 * 2393882 * 2
def baseEnd_2393882 : Nat := 1229212096146508159365743

theorem tailTrace_2393882 : CollatzResearch.WordTrace tailWord_2393882 prefixEnd_2393882 1229212096146508159365743 := by
  unfold tailWord_2393882
  simp only [CollatzResearch.WordTrace]
  refine ⟨21828012378345457835273975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58208033008921220894063933 21828012378345457835273975)
  ·
    refine ⟨32742018567518186752910963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21828012378345457835273975 32742018567518186752910963)
    ·
      refine ⟨49113027851277280129366445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32742018567518186752910963 49113027851277280129366445)
      ·
        refine ⟨18417385444228980048512417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49113027851277280129366445 18417385444228980048512417)
        ·
          refine ⟨13813039083171735036384313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18417385444228980048512417 13813039083171735036384313)
          ·
            refine ⟨10359779312378801277288235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13813039083171735036384313 10359779312378801277288235)
            ·
              refine ⟨15539668968568201915932353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10359779312378801277288235 15539668968568201915932353)
              ·
                refine ⟨11654751726426151436949265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15539668968568201915932353 11654751726426151436949265)
                ·
                  refine ⟨8741063794819613577711949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11654751726426151436949265 8741063794819613577711949)
                  ·
                    refine ⟨3277898923057355091641981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8741063794819613577711949 3277898923057355091641981)
                    ·
                      refine ⟨1229212096146508159365743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3277898923057355091641981 1229212096146508159365743)
                      ·
                        rfl

theorem cell23_2393882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_2393882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393882 prefixEnd_2393882 := by exact prefixLift 2393882
  have htrace : WordTrace (prefixWord ++ tailWord_2393882) baseStart_2393882 baseEnd_2393882 := by
    simpa [prefixWord, tailWord_2393882, baseEnd_2393882] using wordTrace_append hprefix tailTrace_2393882
  have hstable : (prefixWord ++ tailWord_2393882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393882).length < 2 ^ (prefixWord ++ tailWord_2393882).sum := by decide
  have hdescent : baseEnd_2393882 < baseStart_2393882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2393945 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 8]
def baseStart_2393945 : Nat := 118140960795 + 2393945 * 2 ^ 59
def prefixEnd_2393945 : Nat := 4983230072969 + 3 ^ 40 * 2393945 * 2
def baseEnd_2393945 : Nat := 136582716158637934764217

theorem tailTrace_2393945 : CollatzResearch.WordTrace tailWord_2393945 prefixEnd_2393945 136582716158637934764217 := by
  unfold tailWord_2393945
  simp only [CollatzResearch.WordTrace]
  refine ⟨87314347312153593100639289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58209564874769062067092859 87314347312153593100639289)
  ·
    refine ⟨65485760484115194825479467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87314347312153593100639289 65485760484115194825479467)
    ·
      refine ⟨98228640726172792238219201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65485760484115194825479467 98228640726172792238219201)
      ·
        refine ⟨73671480544629594178664401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98228640726172792238219201 73671480544629594178664401)
        ·
          refine ⟨55253610408472195633998301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73671480544629594178664401 55253610408472195633998301)
          ·
            refine ⟨20720103903177073362749363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55253610408472195633998301 20720103903177073362749363)
            ·
              refine ⟨31080155854765610044124045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20720103903177073362749363 31080155854765610044124045)
              ·
                refine ⟨11655058445537103766546517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31080155854765610044124045 11655058445537103766546517)
                ·
                  refine ⟨136582716158637934764217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11655058445537103766546517 136582716158637934764217)
                  ·
                    rfl

theorem cell23_2393945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 8].length) (baseStart_2393945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2393945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2393945 prefixEnd_2393945 := by exact prefixLift 2393945
  have htrace : WordTrace (prefixWord ++ tailWord_2393945) baseStart_2393945 baseEnd_2393945 := by
    simpa [prefixWord, tailWord_2393945, baseEnd_2393945] using wordTrace_append hprefix tailTrace_2393945
  have hstable : (prefixWord ++ tailWord_2393945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2393945).length < 2 ^ (prefixWord ++ tailWord_2393945).sum := by decide
  have hdescent : baseEnd_2393945 < baseStart_2393945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2393945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394033 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 2, 3, 2]
def baseStart_2394033 : Nat := 118140960795 + 2394033 * 2 ^ 59
def prefixEnd_2394033 : Nat := 4983230072969 + 3 ^ 40 * 2394033 * 2
def baseEnd_2394033 : Nat := 1229289631725337068577549

theorem tailTrace_2394033 : CollatzResearch.WordTrace tailWord_2394033 prefixEnd_2394033 1229289631725337068577549 := by
  unfold tailWord_2394033
  simp only [CollatzResearch.WordTrace]
  refine ⟨87317556935834784129842753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58211704623889856086561835 87317556935834784129842753)
  ·
    refine ⟨65488167701876088097382065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87317556935834784129842753 65488167701876088097382065)
    ·
      refine ⟨49116125776407066073036549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65488167701876088097382065 49116125776407066073036549)
      ·
        refine ⟨9209273583076324888694353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49116125776407066073036549 9209273583076324888694353)
        ·
          refine ⟨6906955187307243666520765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9209273583076324888694353 6906955187307243666520765)
          ·
            refine ⟨2590108195240216374945287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6906955187307243666520765 2590108195240216374945287)
            ·
              refine ⟨3885162292860324562417931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590108195240216374945287 3885162292860324562417931)
              ·
                refine ⟨5827743439290486843626897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3885162292860324562417931 5827743439290486843626897)
                ·
                  refine ⟨4370807579467865132720173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5827743439290486843626897 4370807579467865132720173)
                  ·
                    refine ⟨1639052842300449424770065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4370807579467865132720173 1639052842300449424770065)
                    ·
                      refine ⟨1229289631725337068577549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639052842300449424770065 1229289631725337068577549)
                      ·
                        rfl

theorem cell23_2394033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_2394033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394033 prefixEnd_2394033 := by exact prefixLift 2394033
  have htrace : WordTrace (prefixWord ++ tailWord_2394033) baseStart_2394033 baseEnd_2394033 := by
    simpa [prefixWord, tailWord_2394033, baseEnd_2394033] using wordTrace_append hprefix tailTrace_2394033
  have hstable : (prefixWord ++ tailWord_2394033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394033).length < 2 ^ (prefixWord ++ tailWord_2394033).sum := by decide
  have hdescent : baseEnd_2394033 < baseStart_2394033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394042 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_2394042 : Nat := 118140960795 + 2394042 * 2 ^ 59
def prefixEnd_2394042 : Nat := 4983230072969 + 3 ^ 40 * 2394042 * 2
def baseEnd_2394042 : Nat := 1229294253051227533365007

theorem tailTrace_2394042 : CollatzResearch.WordTrace tailWord_2394042 prefixEnd_2394042 1229294253051227533365007 := by
  unfold tailWord_2394042
  simp only [CollatzResearch.WordTrace]
  refine ⟨21829471298200544666730095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58211923461868119111280253 21829471298200544666730095)
  ·
    refine ⟨32744206947300817000095143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21829471298200544666730095 32744206947300817000095143)
    ·
      refine ⟨49116310420951225500142715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32744206947300817000095143 49116310420951225500142715)
      ·
        refine ⟨73674465631426838250214073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49116310420951225500142715 73674465631426838250214073)
        ·
          refine ⟨55255849223570128687660555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73674465631426838250214073 55255849223570128687660555)
          ·
            refine ⟨82883773835355193031490833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55255849223570128687660555 82883773835355193031490833)
            ·
              refine ⟨62162830376516394773618125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82883773835355193031490833 62162830376516394773618125)
              ·
                refine ⟨23311061391193648040106797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62162830376516394773618125 23311061391193648040106797)
                ·
                  refine ⟨8741648021697618015040049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23311061391193648040106797 8741648021697618015040049)
                  ·
                    refine ⟨6556236016273213511280037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8741648021697618015040049 6556236016273213511280037)
                    ·
                      refine ⟨1229294253051227533365007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6556236016273213511280037 1229294253051227533365007)
                      ·
                        rfl

theorem cell23_2394042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_2394042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394042 prefixEnd_2394042 := by exact prefixLift 2394042
  have htrace : WordTrace (prefixWord ++ tailWord_2394042) baseStart_2394042 baseEnd_2394042 := by
    simpa [prefixWord, tailWord_2394042, baseEnd_2394042] using wordTrace_append hprefix tailTrace_2394042
  have hstable : (prefixWord ++ tailWord_2394042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394042).length < 2 ^ (prefixWord ++ tailWord_2394042).sum := by decide
  have hdescent : baseEnd_2394042 < baseStart_2394042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394046 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_2394046 : Nat := 118140960795 + 2394046 * 2 ^ 59
def prefixEnd_2394046 : Nat := 4983230072969 + 3 ^ 40 * 2394046 * 2
def baseEnd_2394046 : Nat := 1229296306973845517714989

theorem tailTrace_2394046 : CollatzResearch.WordTrace tailWord_2394046 prefixEnd_2394046 1229296306973845517714989 := by
  unfold tailWord_2394046
  simp only [CollatzResearch.WordTrace]
  refine ⟨10914753885598460918758249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58212020723191791566710661 10914753885598460918758249)
  ·
    refine ⟨8186065414198845689068687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10914753885598460918758249 8186065414198845689068687)
    ·
      refine ⟨12279098121298268533603031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8186065414198845689068687 12279098121298268533603031)
      ·
        refine ⟨18418647181947402800404547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12279098121298268533603031 18418647181947402800404547)
        ·
          refine ⟨27627970772921104200606821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18418647181947402800404547 27627970772921104200606821)
          ·
            refine ⟨5180244519922707037613779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27627970772921104200606821 5180244519922707037613779)
            ·
              refine ⟨7770366779884060556420669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5180244519922707037613779 7770366779884060556420669)
              ·
                refine ⟨2913887542456522708657751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7770366779884060556420669 2913887542456522708657751)
                ·
                  refine ⟨4370831313684784062986627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2913887542456522708657751 4370831313684784062986627)
                  ·
                    refine ⟨6556246970527176094479941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4370831313684784062986627 6556246970527176094479941)
                    ·
                      refine ⟨1229296306973845517714989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6556246970527176094479941 1229296306973845517714989)
                      ·
                        rfl

theorem cell23_2394046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_2394046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394046 prefixEnd_2394046 := by exact prefixLift 2394046
  have htrace : WordTrace (prefixWord ++ tailWord_2394046) baseStart_2394046 baseEnd_2394046 := by
    simpa [prefixWord, tailWord_2394046, baseEnd_2394046] using wordTrace_append hprefix tailTrace_2394046
  have hstable : (prefixWord ++ tailWord_2394046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394046).length < 2 ^ (prefixWord ++ tailWord_2394046).sum := by decide
  have hdescent : baseEnd_2394046 < baseStart_2394046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394056 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 2, 4]
def baseStart_2394056 : Nat := 118140960795 + 2394056 * 2 ^ 59
def prefixEnd_2394056 : Nat := 4983230072969 + 3 ^ 40 * 2394056 * 2
def baseEnd_2394056 : Nat := 409767147260130159529981

theorem tailTrace_2394056 : CollatzResearch.WordTrace tailWord_2394056 prefixEnd_2394056 409767147260130159529981 := by
  unfold tailWord_2394056
  simp only [CollatzResearch.WordTrace]
  refine ⟨43659197907375729528965011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58212263876500972705286681 43659197907375729528965011)
  ·
    refine ⟨65488796861063594293447517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43659197907375729528965011 65488796861063594293447517)
    ·
      refine ⟨24558298822898847860042819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65488796861063594293447517 24558298822898847860042819)
      ·
        refine ⟨36837448234348271790064229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24558298822898847860042819 36837448234348271790064229)
        ·
          refine ⟨6907021543940300960637043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36837448234348271790064229 6907021543940300960637043)
          ·
            refine ⟨10360532315910451440955565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6907021543940300960637043 10360532315910451440955565)
            ·
              refine ⟨3885199618466419290358337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10360532315910451440955565 3885199618466419290358337)
              ·
                refine ⟨2913899713849814467768753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3885199618466419290358337 2913899713849814467768753)
                ·
                  refine ⟨2185424785387360850826565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2913899713849814467768753 2185424785387360850826565)
                  ·
                    refine ⟨409767147260130159529981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2185424785387360850826565 409767147260130159529981)
                    ·
                      rfl

theorem cell23_2394056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_2394056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394056 prefixEnd_2394056 := by exact prefixLift 2394056
  have htrace : WordTrace (prefixWord ++ tailWord_2394056) baseStart_2394056 baseEnd_2394056 := by
    simpa [prefixWord, tailWord_2394056, baseEnd_2394056] using wordTrace_append hprefix tailTrace_2394056
  have hstable : (prefixWord ++ tailWord_2394056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394056).length < 2 ^ (prefixWord ++ tailWord_2394056).sum := by decide
  have hdescent : baseEnd_2394056 < baseStart_2394056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394063 : List Nat := [1, 1, 2, 1, 1, 5, 1, 6, 1, 2, 2]
def baseStart_2394063 : Nat := 118140960795 + 2394063 * 2 ^ 59
def prefixEnd_2394063 : Nat := 4983230072969 + 3 ^ 40 * 2394063 * 2
def baseEnd_2394063 : Nat := 1229305036144971951202411

theorem tailTrace_2394063 : CollatzResearch.WordTrace tailWord_2394063 prefixEnd_2394063 1229305036144971951202411 := by
  unfold tailWord_2394063
  simp only [CollatzResearch.WordTrace]
  refine ⟨87318651125726099253434843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58212434083817399502289895 87318651125726099253434843)
  ·
    refine ⟨130977976688589148880152265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87318651125726099253434843 130977976688589148880152265)
    ·
      refine ⟨98233482516441861660114199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130977976688589148880152265 98233482516441861660114199)
      ·
        refine ⟨147350223774662792490171299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98233482516441861660114199 147350223774662792490171299)
        ·
          refine ⟨221025335661994188735256949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147350223774662792490171299 221025335661994188735256949)
          ·
            refine ⟨20721125218311955193930339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221025335661994188735256949 20721125218311955193930339)
            ·
              refine ⟨31081687827467932790895509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20721125218311955193930339 31081687827467932790895509)
              ·
                refine ⟨1456954116912559349573227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31081687827467932790895509 1456954116912559349573227)
                ·
                  refine ⟨2185431175368839024359841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456954116912559349573227 2185431175368839024359841)
                  ·
                    refine ⟨1639073381526629268269881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2185431175368839024359841 1639073381526629268269881)
                    ·
                      refine ⟨1229305036144971951202411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639073381526629268269881 1229305036144971951202411)
                      ·
                        rfl

theorem cell23_2394063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 1, 2, 2].length) (baseStart_2394063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394063 prefixEnd_2394063 := by exact prefixLift 2394063
  have htrace : WordTrace (prefixWord ++ tailWord_2394063) baseStart_2394063 baseEnd_2394063 := by
    simpa [prefixWord, tailWord_2394063, baseEnd_2394063] using wordTrace_append hprefix tailTrace_2394063
  have hstable : (prefixWord ++ tailWord_2394063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394063).length < 2 ^ (prefixWord ++ tailWord_2394063).sum := by decide
  have hdescent : baseEnd_2394063 < baseStart_2394063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394066 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2394066 : Nat := 118140960795 + 2394066 * 2 ^ 59
def prefixEnd_2394066 : Nat := 4983230072969 + 3 ^ 40 * 2394066 * 2
def baseEnd_2394066 : Nat := 1229306576586935439464897

theorem tailTrace_2394066 : CollatzResearch.WordTrace tailWord_2394066 prefixEnd_2394066 1229306576586935439464897 := by
  unfold tailWord_2394066
  simp only [CollatzResearch.WordTrace]
  refine ⟨21829690136178807691448513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58212507029810153843862701 21829690136178807691448513)
  ·
    refine ⟨16372267602134105768586385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21829690136178807691448513 16372267602134105768586385)
    ·
      refine ⟨12279200701600579326439789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16372267602134105768586385 12279200701600579326439789)
      ·
        refine ⟨4604700263100217247414921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12279200701600579326439789 4604700263100217247414921)
        ·
          refine ⟨3453525197325162935561191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4604700263100217247414921 3453525197325162935561191)
          ·
            refine ⟨5180287795987744403341787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3453525197325162935561191 5180287795987744403341787)
            ·
              refine ⟨7770431693981616605012681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5180287795987744403341787 7770431693981616605012681)
              ·
                refine ⟨5827823770486212453759511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7770431693981616605012681 5827823770486212453759511)
                ·
                  refine ⟨8741735655729318680639267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5827823770486212453759511 8741735655729318680639267)
                  ·
                    refine ⟨13112603483593978020958901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8741735655729318680639267 13112603483593978020958901)
                    ·
                      refine ⟨1229306576586935439464897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13112603483593978020958901 1229306576586935439464897)
                      ·
                        rfl

theorem cell23_2394066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2394066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394066 prefixEnd_2394066 := by exact prefixLift 2394066
  have htrace : WordTrace (prefixWord ++ tailWord_2394066) baseStart_2394066 baseEnd_2394066 := by
    simpa [prefixWord, tailWord_2394066, baseEnd_2394066] using wordTrace_append hprefix tailTrace_2394066
  have hstable : (prefixWord ++ tailWord_2394066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394066).length < 2 ^ (prefixWord ++ tailWord_2394066).sum := by decide
  have hdescent : baseEnd_2394066 < baseStart_2394066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394073 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 2, 4]
def baseStart_2394073 : Nat := 118140960795 + 2394073 * 2 ^ 59
def prefixEnd_2394073 : Nat := 4983230072969 + 3 ^ 40 * 2394073 * 2
def baseEnd_2394073 : Nat := 409770056983838970692455

theorem tailTrace_2394073 : CollatzResearch.WordTrace tailWord_2394073 prefixEnd_2394073 409770056983838970692455 := by
  unfold tailWord_2394073
  simp only [CollatzResearch.WordTrace]
  refine ⟨87319015855689870961298873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58212677237126580640865915 87319015855689870961298873)
  ·
    refine ⟨65489261891767403220974155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87319015855689870961298873 65489261891767403220974155)
    ·
      refine ⟨98233892837651104831461233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65489261891767403220974155 98233892837651104831461233)
      ·
        refine ⟨73675419628238328623595925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98233892837651104831461233 73675419628238328623595925)
        ·
          refine ⟨3453535295073671654231059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73675419628238328623595925 3453535295073671654231059)
          ·
            refine ⟨5180302942610507481346589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3453535295073671654231059 5180302942610507481346589)
            ·
              refine ⟨1942613603478940305504971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5180302942610507481346589 1942613603478940305504971)
              ·
                refine ⟨2913920405218410458257457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1942613603478940305504971 2913920405218410458257457)
                ·
                  refine ⟨2185440303913807843693093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2913920405218410458257457 2185440303913807843693093)
                  ·
                    refine ⟨409770056983838970692455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2185440303913807843693093 409770056983838970692455)
                    ·
                      rfl

theorem cell23_2394073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 2, 4].length) (baseStart_2394073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394073 prefixEnd_2394073 := by exact prefixLift 2394073
  have htrace : WordTrace (prefixWord ++ tailWord_2394073) baseStart_2394073 baseEnd_2394073 := by
    simpa [prefixWord, tailWord_2394073, baseEnd_2394073] using wordTrace_append hprefix tailTrace_2394073
  have hstable : (prefixWord ++ tailWord_2394073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394073).length < 2 ^ (prefixWord ++ tailWord_2394073).sum := by decide
  have hdescent : baseEnd_2394073 < baseStart_2394073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394097 : List Nat := [1, 2, 2, 2, 5, 2, 1, 3, 1, 2, 2]
def baseStart_2394097 : Nat := 118140960795 + 2394097 * 2 ^ 59
def prefixEnd_2394097 : Nat := 4983230072969 + 3 ^ 40 * 2394097 * 2
def baseEnd_2394097 : Nat := 1229322494487224818177255

theorem tailTrace_2394097 : CollatzResearch.WordTrace tailWord_2394097 prefixEnd_2394097 1229322494487224818177255 := by
  unfold tailWord_2394097
  simp only [CollatzResearch.WordTrace]
  refine ⟨87319891207602923060172545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58213260805068615373448363 87319891207602923060172545)
  ·
    refine ⟨65489918405702192295129409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87319891207602923060172545 65489918405702192295129409)
    ·
      refine ⟨49117438804276644221347057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65489918405702192295129409 49117438804276644221347057)
      ·
        refine ⟨36838079103207483166010293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49117438804276644221347057 36838079103207483166010293)
        ·
          refine ⟨3453569915925701546813465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36838079103207483166010293 3453569915925701546813465)
          ·
            refine ⟨2590177436944276160110099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3453569915925701546813465 2590177436944276160110099)
            ·
              refine ⟨3885266155416414240165149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590177436944276160110099 3885266155416414240165149)
              ·
                refine ⟨1456974808281155340061931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3885266155416414240165149 1456974808281155340061931)
                ·
                  refine ⟨2185462212421733010092897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456974808281155340061931 2185462212421733010092897)
                  ·
                    refine ⟨1639096659316299757569673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2185462212421733010092897 1639096659316299757569673)
                    ·
                      refine ⟨1229322494487224818177255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639096659316299757569673 1229322494487224818177255)
                      ·
                        rfl

theorem cell23_2394097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_2394097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394097 prefixEnd_2394097 := by exact prefixLift 2394097
  have htrace : WordTrace (prefixWord ++ tailWord_2394097) baseStart_2394097 baseEnd_2394097 := by
    simpa [prefixWord, tailWord_2394097, baseEnd_2394097] using wordTrace_append hprefix tailTrace_2394097
  have hstable : (prefixWord ++ tailWord_2394097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394097).length < 2 ^ (prefixWord ++ tailWord_2394097).sum := by decide
  have hdescent : baseEnd_2394097 < baseStart_2394097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394112 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 2, 6]
def baseStart_2394112 : Nat := 118140960795 + 2394112 * 2 ^ 59
def prefixEnd_2394112 : Nat := 4983230072969 + 3 ^ 40 * 2394112 * 2
def baseEnd_2394112 : Nat := 409776732232347419829895

theorem tailTrace_2394112 : CollatzResearch.WordTrace tailWord_2394112 prefixEnd_2394112 409776732232347419829895 := by
  unfold tailWord_2394112
  simp only [CollatzResearch.WordTrace]
  refine ⟨43660219151274290310984295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58213625535032387081312393 43660219151274290310984295)
  ·
    refine ⟨65490328726911435466476443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43660219151274290310984295 65490328726911435466476443)
    ·
      refine ⟨98235493090367153199714665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65490328726911435466476443 98235493090367153199714665)
      ·
        refine ⟨73676619817775364899785999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98235493090367153199714665 73676619817775364899785999)
        ·
          refine ⟨110514929726663047349678999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73676619817775364899785999 110514929726663047349678999)
          ·
            refine ⟨165772394589994571024518499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110514929726663047349678999 165772394589994571024518499)
            ·
              refine ⟨248658591884991856536777749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165772394589994571024518499 248658591884991856536777749)
              ·
                refine ⟨11655871494608993275161457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 248658591884991856536777749 11655871494608993275161457)
                ·
                  refine ⟨8741903620956744956371093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11655871494608993275161457 8741903620956744956371093)
                  ·
                    refine ⟨409776732232347419829895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8741903620956744956371093 409776732232347419829895)
                    ·
                      rfl

theorem cell23_2394112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_2394112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394112 prefixEnd_2394112 := by exact prefixLift 2394112
  have htrace : WordTrace (prefixWord ++ tailWord_2394112) baseStart_2394112 baseEnd_2394112 := by
    simpa [prefixWord, tailWord_2394112, baseEnd_2394112] using wordTrace_append hprefix tailTrace_2394112
  have hstable : (prefixWord ++ tailWord_2394112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394112).length < 2 ^ (prefixWord ++ tailWord_2394112).sum := by decide
  have hdescent : baseEnd_2394112 < baseStart_2394112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394136 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 1, 4, 2]
def baseStart_2394136 : Nat := 118140960795 + 2394136 * 2 ^ 59
def prefixEnd_2394136 : Nat := 4983230072969 + 3 ^ 40 * 2394136 * 2
def baseEnd_2394136 : Nat := 1229342520232750165589575

theorem tailTrace_2394136 : CollatzResearch.WordTrace tailWord_2394136 prefixEnd_2394136 1229342520232750165589575 := by
  unfold tailWord_2394136
  simp only [CollatzResearch.WordTrace]
  refine ⟨43660656827230816360421131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58214209102974421813894841 43660656827230816360421131)
  ·
    refine ⟨65490985240846224540631697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43660656827230816360421131 65490985240846224540631697)
    ·
      refine ⟨49118238930634668405473773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65490985240846224540631697 49118238930634668405473773)
      ·
        refine ⟨18419339598988000652052665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49118238930634668405473773 18419339598988000652052665)
        ·
          refine ⟨13814504699241000489039499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18419339598988000652052665 13814504699241000489039499)
          ·
            refine ⟨20721757048861500733559249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13814504699241000489039499 20721757048861500733559249)
            ·
              refine ⟨15541317786646125550169437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20721757048861500733559249 15541317786646125550169437)
              ·
                refine ⟨5827994169992297081313539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15541317786646125550169437 5827994169992297081313539)
                ·
                  refine ⟨8741991254988445621970309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5827994169992297081313539 8741991254988445621970309)
                  ·
                    refine ⟨1639123360310333554119433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8741991254988445621970309 1639123360310333554119433)
                    ·
                      refine ⟨1229342520232750165589575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639123360310333554119433 1229342520232750165589575)
                      ·
                        rfl

theorem cell23_2394136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_2394136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394136 prefixEnd_2394136 := by exact prefixLift 2394136
  have htrace : WordTrace (prefixWord ++ tailWord_2394136) baseStart_2394136 baseEnd_2394136 := by
    simpa [prefixWord, tailWord_2394136, baseEnd_2394136] using wordTrace_append hprefix tailTrace_2394136
  have hstable : (prefixWord ++ tailWord_2394136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394136).length < 2 ^ (prefixWord ++ tailWord_2394136).sum := by decide
  have hdescent : baseEnd_2394136 < baseStart_2394136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394140 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_2394140 : Nat := 118140960795 + 2394140 * 2 ^ 59
def prefixEnd_2394140 : Nat := 4983230072969 + 3 ^ 40 * 2394140 * 2
def baseEnd_2394140 : Nat := 1229344574155368149939557

theorem tailTrace_2394140 : CollatzResearch.WordTrace tailWord_2394140 prefixEnd_2394140 1229344574155368149939557 := by
  unfold tailWord_2394140
  simp only [CollatzResearch.WordTrace]
  refine ⟨43660729773223570701993937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58214306364298094269325249 43660729773223570701993937)
  ·
    refine ⟨32745547329917678026495453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43660729773223570701993937 32745547329917678026495453)
    ·
      refine ⟨12279580248719129259935795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32745547329917678026495453 12279580248719129259935795)
      ·
        refine ⟨18419370373078693889903693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12279580248719129259935795 18419370373078693889903693)
        ·
          refine ⟨6907263889904510208713885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18419370373078693889903693 6907263889904510208713885)
          ·
            refine ⟨2590223958714191328267707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6907263889904510208713885 2590223958714191328267707)
            ·
              refine ⟨3885335938071286992401561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590223958714191328267707 3885335938071286992401561)
              ·
                refine ⟨2914001953553465244301171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3885335938071286992401561 2914001953553465244301171)
                ·
                  refine ⟨4371002930330197866451757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2914001953553465244301171 4371002930330197866451757)
                  ·
                    refine ⟨1639126098873824199919409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4371002930330197866451757 1639126098873824199919409)
                    ·
                      refine ⟨1229344574155368149939557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639126098873824199919409 1229344574155368149939557)
                      ·
                        rfl

theorem cell23_2394140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_2394140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394140 prefixEnd_2394140 := by exact prefixLift 2394140
  have htrace : WordTrace (prefixWord ++ tailWord_2394140) baseStart_2394140 baseEnd_2394140 := by
    simpa [prefixWord, tailWord_2394140, baseEnd_2394140] using wordTrace_append hprefix tailTrace_2394140
  have hstable : (prefixWord ++ tailWord_2394140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394140).length < 2 ^ (prefixWord ++ tailWord_2394140).sum := by decide
  have hdescent : baseEnd_2394140 < baseStart_2394140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394166 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2394166 : Nat := 118140960795 + 2394166 * 2 ^ 59
def prefixEnd_2394166 : Nat := 4983230072969 + 3 ^ 40 * 2394166 * 2
def baseEnd_2394166 : Nat := 1229357924652385048214437

theorem tailTrace_2394166 : CollatzResearch.WordTrace tailWord_2394166 prefixEnd_2394166 1229357924652385048214437 := by
  unfold tailWord_2394166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5457650490272059240277147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58214938562901965229622901 5457650490272059240277147)
  ·
    refine ⟨8186475735408088860415721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5457650490272059240277147 8186475735408088860415721)
    ·
      refine ⟨6139856801556066645311791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8186475735408088860415721 6139856801556066645311791)
      ·
        refine ⟨9209785202334099967967687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6139856801556066645311791 9209785202334099967967687)
        ·
          refine ⟨13814677803501149951951531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9209785202334099967967687 13814677803501149951951531)
          ·
            refine ⟨20722016705251724927927297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13814677803501149951951531 20722016705251724927927297)
            ·
              refine ⟨15541512528938793695945473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20722016705251724927927297 15541512528938793695945473)
              ·
                refine ⟨11656134396704095271959105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15541512528938793695945473 11656134396704095271959105)
                ·
                  refine ⟨8742100797528071453969329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11656134396704095271959105 8742100797528071453969329)
                  ·
                    refine ⟨6556575598146053590476997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8742100797528071453969329 6556575598146053590476997)
                    ·
                      refine ⟨1229357924652385048214437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6556575598146053590476997 1229357924652385048214437)
                      ·
                        rfl

theorem cell23_2394166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2394166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394166 prefixEnd_2394166 := by exact prefixLift 2394166
  have htrace : WordTrace (prefixWord ++ tailWord_2394166) baseStart_2394166 baseEnd_2394166 := by
    simpa [prefixWord, tailWord_2394166, baseEnd_2394166] using wordTrace_append hprefix tailTrace_2394166
  have hstable : (prefixWord ++ tailWord_2394166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394166).length < 2 ^ (prefixWord ++ tailWord_2394166).sum := by decide
  have hdescent : baseEnd_2394166 < baseStart_2394166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394176 : List Nat := [2, 1, 1, 2, 2, 5, 1, 4, 5]
def baseStart_2394176 : Nat := 118140960795 + 2394176 * 2 ^ 59
def prefixEnd_2394176 : Nat := 4983230072969 + 3 ^ 40 * 2394176 * 2
def baseEnd_2394176 : Nat := 136595895495436667676599

theorem tailTrace_2394176 : CollatzResearch.WordTrace tailWord_2394176 prefixEnd_2394176 136595895495436667676599 := by
  unfold tailWord_2394176
  simp only [CollatzResearch.WordTrace]
  refine ⟨43661386287158359776149191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58215181716211146368198921 43661386287158359776149191)
  ·
    refine ⟨65492079430737539664223787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43661386287158359776149191 65492079430737539664223787)
    ·
      refine ⟨98238119146106309496335681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65492079430737539664223787 98238119146106309496335681)
      ·
        refine ⟨73678589359579732122251761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98238119146106309496335681 73678589359579732122251761)
        ·
          refine ⟨55258942019684799091688821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73678589359579732122251761 55258942019684799091688821)
          ·
            refine ⟨5180525814345449914845827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55258942019684799091688821 5180525814345449914845827)
            ·
              refine ⟨7770788721518174872268741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5180525814345449914845827 7770788721518174872268741)
              ·
                refine ⟨1457022885284657788550389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7770788721518174872268741 1457022885284657788550389)
                ·
                  refine ⟨136595895495436667676599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1457022885284657788550389 136595895495436667676599)
                  ·
                    rfl

theorem cell23_2394176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 5].length) (baseStart_2394176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394176 prefixEnd_2394176 := by exact prefixLift 2394176
  have htrace : WordTrace (prefixWord ++ tailWord_2394176) baseStart_2394176 baseEnd_2394176 := by
    simpa [prefixWord, tailWord_2394176, baseEnd_2394176] using wordTrace_append hprefix tailTrace_2394176
  have hstable : (prefixWord ++ tailWord_2394176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394176).length < 2 ^ (prefixWord ++ tailWord_2394176).sum := by decide
  have hdescent : baseEnd_2394176 < baseStart_2394176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394196 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_2394196 : Nat := 118140960795 + 2394196 * 2 ^ 59
def prefixEnd_2394196 : Nat := 4983230072969 + 3 ^ 40 * 2394196 * 2
def baseEnd_2394196 : Nat := 1229373329072019930839299

theorem tailTrace_2394196 : CollatzResearch.WordTrace tailWord_2394196 prefixEnd_2394196 1229373329072019930839299 := by
  unfold tailWord_2394196
  simp only [CollatzResearch.WordTrace]
  refine ⟨43661751017122131484013221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58215668022829508645350961 43661751017122131484013221)
  ·
    refine ⟨8186578315710399653252479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43661751017122131484013221 8186578315710399653252479)
    ·
      refine ⟨12279867473565599479878719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8186578315710399653252479 12279867473565599479878719)
      ·
        refine ⟨18419801210348399219818079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12279867473565599479878719 18419801210348399219818079)
        ·
          refine ⟨27629701815522598829727119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18419801210348399219818079 27629701815522598829727119)
          ·
            refine ⟨41444552723283898244590679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27629701815522598829727119 41444552723283898244590679)
            ·
              refine ⟨62166829084925847366886019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41444552723283898244590679 62166829084925847366886019)
              ·
                refine ⟨93250243627388771050329029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62166829084925847366886019 93250243627388771050329029)
                ·
                  refine ⟨17484420680135394571936693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93250243627388771050329029 17484420680135394571936693)
                  ·
                    refine ⟨1639164438762693241119065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17484420680135394571936693 1639164438762693241119065)
                    ·
                      refine ⟨1229373329072019930839299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639164438762693241119065 1229373329072019930839299)
                      ·
                        rfl

theorem cell23_2394196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_2394196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394196 prefixEnd_2394196 := by exact prefixLift 2394196
  have htrace : WordTrace (prefixWord ++ tailWord_2394196) baseStart_2394196 baseEnd_2394196 := by
    simpa [prefixWord, tailWord_2394196, baseEnd_2394196] using wordTrace_append hprefix tailTrace_2394196
  have hstable : (prefixWord ++ tailWord_2394196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394196).length < 2 ^ (prefixWord ++ tailWord_2394196).sum := by decide
  have hdescent : baseEnd_2394196 < baseStart_2394196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394210 : List Nat := [3, 3, 2, 2, 2, 1, 2, 3, 5]
def baseStart_2394210 : Nat := 118140960795 + 2394210 * 2 ^ 59
def prefixEnd_2394210 : Nat := 4983230072969 + 3 ^ 40 * 2394210 * 2
def baseEnd_2394210 : Nat := 136597835311242541784915

theorem tailTrace_2394210 : CollatzResearch.WordTrace tailWord_2394210 prefixEnd_2394210 136597835311242541784915 := by
  unfold tailWord_2394210
  simp only [CollatzResearch.WordTrace]
  refine ⟨21831003164048385839759021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58216008437462362239357389 21831003164048385839759021)
  ·
    refine ⟨8186626186518144689909633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21831003164048385839759021 8186626186518144689909633)
    ·
      refine ⟨6139969639888608517432225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8186626186518144689909633 6139969639888608517432225)
      ·
        refine ⟨4604977229916456388074169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6139969639888608517432225 4604977229916456388074169)
        ·
          refine ⟨3453732922437342291055627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4604977229916456388074169 3453732922437342291055627)
          ·
            refine ⟨5180599383656013436583441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3453732922437342291055627 5180599383656013436583441)
            ·
              refine ⟨3885449537742010077437581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5180599383656013436583441 3885449537742010077437581)
              ·
                refine ⟨1457043576653253779039093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3885449537742010077437581 1457043576653253779039093)
                ·
                  refine ⟨136597835311242541784915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1457043576653253779039093 136597835311242541784915)
                  ·
                    rfl

theorem cell23_2394210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_2394210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394210 prefixEnd_2394210 := by exact prefixLift 2394210
  have htrace : WordTrace (prefixWord ++ tailWord_2394210) baseStart_2394210 baseEnd_2394210 := by
    simpa [prefixWord, tailWord_2394210, baseEnd_2394210] using wordTrace_append hprefix tailTrace_2394210
  have hstable : (prefixWord ++ tailWord_2394210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394210).length < 2 ^ (prefixWord ++ tailWord_2394210).sum := by decide
  have hdescent : baseEnd_2394210 < baseStart_2394210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394236 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 3, 4]
def baseStart_2394236 : Nat := 118140960795 + 2394236 * 2 ^ 59
def prefixEnd_2394236 : Nat := 4983230072969 + 3 ^ 40 * 2394236 * 2
def baseEnd_2394236 : Nat := 409797956099399924779705

theorem tailTrace_2394236 : CollatzResearch.WordTrace tailWord_2394236 prefixEnd_2394236 409797956099399924779705 := by
  unfold tailWord_2394236
  simp only [CollatzResearch.WordTrace]
  refine ⟨43662480477049674899741281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58216640636066233199655041 43662480477049674899741281)
  ·
    refine ⟨32746860357787256174805961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43662480477049674899741281 32746860357787256174805961)
    ·
      refine ⟨24560145268340442131104471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32746860357787256174805961 24560145268340442131104471)
      ·
        refine ⟨36840217902510663196656707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24560145268340442131104471 36840217902510663196656707)
        ·
          refine ⟨55260326853765994794985061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36840217902510663196656707 55260326853765994794985061)
          ·
            refine ⟨10361311285081124024059699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55260326853765994794985061 10361311285081124024059699)
            ·
              refine ⟨15541966927621686036089549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10361311285081124024059699 15541966927621686036089549)
              ·
                refine ⟨5828237597858132263533581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15541966927621686036089549 5828237597858132263533581)
                ·
                  refine ⟨2185589099196799598825093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5828237597858132263533581 2185589099196799598825093)
                  ·
                    refine ⟨409797956099399924779705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2185589099196799598825093 409797956099399924779705)
                    ·
                      rfl

theorem cell23_2394236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_2394236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394236 prefixEnd_2394236 := by exact prefixLift 2394236
  have htrace : WordTrace (prefixWord ++ tailWord_2394236) baseStart_2394236 baseEnd_2394236 := by
    simpa [prefixWord, tailWord_2394236, baseEnd_2394236] using wordTrace_append hprefix tailTrace_2394236
  have hstable : (prefixWord ++ tailWord_2394236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394236).length < 2 ^ (prefixWord ++ tailWord_2394236).sum := by decide
  have hdescent : baseEnd_2394236 < baseStart_2394236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394259 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 3]
def baseStart_2394259 : Nat := 118140960795 + 2394259 * 2 ^ 59
def prefixEnd_2394259 : Nat := 4983230072969 + 3 ^ 40 * 2394259 * 2
def baseEnd_2394259 : Nat := 1229405678353253184351509

theorem tailTrace_2394259 : CollatzResearch.WordTrace tailWord_2394259 prefixEnd_2394259 1229405678353253184351509 := by
  unfold tailWord_2394259
  simp only [CollatzResearch.WordTrace]
  refine ⟨87325799833016024727569831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58217199888677349818379887 87325799833016024727569831)
  ·
    refine ⟨130988699749524037091354747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87325799833016024727569831 130988699749524037091354747)
    ·
      refine ⟨196483049624286055637032121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130988699749524037091354747 196483049624286055637032121)
      ·
        refine ⟨147362287218214541727774091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196483049624286055637032121 147362287218214541727774091)
        ·
          refine ⟨221043430827321812591661137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147362287218214541727774091 221043430827321812591661137)
          ·
            refine ⟨165782573120491359443745853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221043430827321812591661137 165782573120491359443745853)
            ·
              refine ⟨62168464920184259791404695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165782573120491359443745853 62168464920184259791404695)
              ·
                refine ⟨93252697380276389687107043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62168464920184259791404695 93252697380276389687107043)
                ·
                  refine ⟨139879046070414584530660565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93252697380276389687107043 139879046070414584530660565)
                  ·
                    refine ⟨3278415142275341824937357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 139879046070414584530660565 3278415142275341824937357)
                    ·
                      refine ⟨1229405678353253184351509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3278415142275341824937357 1229405678353253184351509)
                      ·
                        rfl

theorem cell23_2394259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 3].length) (baseStart_2394259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394259 prefixEnd_2394259 := by exact prefixLift 2394259
  have htrace : WordTrace (prefixWord ++ tailWord_2394259) baseStart_2394259 baseEnd_2394259 := by
    simpa [prefixWord, tailWord_2394259, baseEnd_2394259] using wordTrace_append hprefix tailTrace_2394259
  have hstable : (prefixWord ++ tailWord_2394259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394259).length < 2 ^ (prefixWord ++ tailWord_2394259).sum := by decide
  have hdescent : baseEnd_2394259 < baseStart_2394259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394300 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 6]
def baseStart_2394300 : Nat := 118140960795 + 2394300 * 2 ^ 59
def prefixEnd_2394300 : Nat := 4983230072969 + 3 ^ 40 * 2394300 * 2
def baseEnd_2394300 : Nat := 136602970117787502659869

theorem tailTrace_2394300 : CollatzResearch.WordTrace tailWord_2394300 prefixEnd_2394300 136602970117787502659869 := by
  unfold tailWord_2394300
  simp only [CollatzResearch.WordTrace]
  refine ⟨43663647612933744364906177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58218196817244992486541569 43663647612933744364906177)
  ·
    refine ⟨32747735709700308273679633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43663647612933744364906177 32747735709700308273679633)
    ·
      refine ⟨24560801782275231205259725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32747735709700308273679633 24560801782275231205259725)
      ·
        refine ⟨9210300668353211701972397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24560801782275231205259725 9210300668353211701972397)
        ·
          refine ⟨3453862750632454388239649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9210300668353211701972397 3453862750632454388239649)
          ·
            refine ⟨2590397062974340791179737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3453862750632454388239649 2590397062974340791179737)
            ·
              refine ⟨1942797797230755593384803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2590397062974340791179737 1942797797230755593384803)
              ·
                refine ⟨2914196695846133390077205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1942797797230755593384803 2914196695846133390077205)
                ·
                  refine ⟨136602970117787502659869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2914196695846133390077205 136602970117787502659869)
                  ·
                    rfl

theorem cell23_2394300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_2394300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394300 prefixEnd_2394300 := by exact prefixLift 2394300
  have htrace : WordTrace (prefixWord ++ tailWord_2394300) baseStart_2394300 baseEnd_2394300 := by
    simpa [prefixWord, tailWord_2394300, baseEnd_2394300] using wordTrace_append hprefix tailTrace_2394300
  have hstable : (prefixWord ++ tailWord_2394300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394300).length < 2 ^ (prefixWord ++ tailWord_2394300).sum := by decide
  have hdescent : baseEnd_2394300 < baseStart_2394300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394338 : List Nat := [3, 3, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2394338 : Nat := 118140960795 + 2394338 * 2 ^ 59
def prefixEnd_2394338 : Nat := 4983230072969 + 3 ^ 40 * 2394338 * 2
def baseEnd_2394338 : Nat := 409815414441652791754549

theorem tailTrace_2394338 : CollatzResearch.WordTrace tailWord_2394338 prefixEnd_2394338 409815414441652791754549 := by
  unfold tailWord_2394338
  simp only [CollatzResearch.WordTrace]
  refine ⟨21832170299932455304923917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58219120799819880813130445 21832170299932455304923917)
  ·
    refine ⟨8187063862474670739346469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21832170299932455304923917 8187063862474670739346469)
    ·
      refine ⟨1535074474214000763627463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8187063862474670739346469 1535074474214000763627463)
      ·
        refine ⟨2302611711321001145441195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535074474214000763627463 2302611711321001145441195)
        ·
          refine ⟨3453917566981501718161793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2302611711321001145441195 3453917566981501718161793)
          ·
            refine ⟨2590438175236126288621345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3453917566981501718161793 2590438175236126288621345)
            ·
              refine ⟨1942828631427094716466009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2590438175236126288621345 1942828631427094716466009)
              ·
                refine ⟨1457121473570321037349507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942828631427094716466009 1457121473570321037349507)
                ·
                  refine ⟨2185682210355481556024261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457121473570321037349507 2185682210355481556024261)
                  ·
                    refine ⟨409815414441652791754549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2185682210355481556024261 409815414441652791754549)
                    ·
                      rfl

theorem cell23_2394338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2394338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394338 prefixEnd_2394338 := by exact prefixLift 2394338
  have htrace : WordTrace (prefixWord ++ tailWord_2394338) baseStart_2394338 baseEnd_2394338 := by
    simpa [prefixWord, tailWord_2394338, baseEnd_2394338] using wordTrace_append hprefix tailTrace_2394338
  have hstable : (prefixWord ++ tailWord_2394338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394338).length < 2 ^ (prefixWord ++ tailWord_2394338).sum := by decide
  have hdescent : baseEnd_2394338 < baseStart_2394338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394344 : List Nat := [2, 1, 4, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_2394344 : Nat := 118140960795 + 2394344 * 2 ^ 59
def prefixEnd_2394344 : Nat := 4983230072969 + 3 ^ 40 * 2394344 * 2
def baseEnd_2394344 : Nat := 1229449324208885351788619

theorem tailTrace_2394344 : CollatzResearch.WordTrace tailWord_2394344 prefixEnd_2394344 1229449324208885351788619 := by
  unfold tailWord_2394344
  simp only [CollatzResearch.WordTrace]
  refine ⟨43664450018854042122207043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58219266691805389496276057 43664450018854042122207043)
  ·
    refine ⟨65496675028281063183310565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43664450018854042122207043 65496675028281063183310565)
    ·
      refine ⟨12280626567802699346870731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65496675028281063183310565 12280626567802699346870731)
      ·
        refine ⟨18420939851704049020306097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12280626567802699346870731 18420939851704049020306097)
        ·
          refine ⟨13815704888778036765229573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18420939851704049020306097 13815704888778036765229573)
          ·
            refine ⟨2590444666645881893480545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13815704888778036765229573 2590444666645881893480545)
            ·
              refine ⟨1942833499984411420110409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2590444666645881893480545 1942833499984411420110409)
              ·
                refine ⟨1457125124988308565082807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942833499984411420110409 1457125124988308565082807)
                ·
                  refine ⟨2185687687482462847624211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457125124988308565082807 2185687687482462847624211)
                  ·
                    refine ⟨3278531531223694271436317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2185687687482462847624211 3278531531223694271436317)
                    ·
                      refine ⟨1229449324208885351788619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3278531531223694271436317 1229449324208885351788619)
                      ·
                        rfl

theorem cell23_2394344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_2394344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394344 prefixEnd_2394344 := by exact prefixLift 2394344
  have htrace : WordTrace (prefixWord ++ tailWord_2394344) baseStart_2394344 baseEnd_2394344 := by
    simpa [prefixWord, tailWord_2394344, baseEnd_2394344] using wordTrace_append hprefix tailTrace_2394344
  have hstable : (prefixWord ++ tailWord_2394344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394344).length < 2 ^ (prefixWord ++ tailWord_2394344).sum := by decide
  have hdescent : baseEnd_2394344 < baseStart_2394344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394346 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2394346 : Nat := 118140960795 + 2394346 * 2 ^ 59
def prefixEnd_2394346 : Nat := 4983230072969 + 3 ^ 40 * 2394346 * 2
def baseEnd_2394346 : Nat := 1229450351170194343963609

theorem tailTrace_2394346 : CollatzResearch.WordTrace tailWord_2394346 prefixEnd_2394346 1229450351170194343963609 := by
  unfold tailWord_2394346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21832243245925209646496723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58219315322467225723991261 21832243245925209646496723)
  ·
    refine ⟨32748364868887814469745085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21832243245925209646496723 32748364868887814469745085)
    ·
      refine ⟨12280636825832930426154407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32748364868887814469745085 12280636825832930426154407)
      ·
        refine ⟨18420955238749395639231611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12280636825832930426154407 18420955238749395639231611)
        ·
          refine ⟨27631432858124093458847417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18420955238749395639231611 27631432858124093458847417)
          ·
            refine ⟨20723574643593070094135563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27631432858124093458847417 20723574643593070094135563)
            ·
              refine ⟨31085361965389605141203345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20723574643593070094135563 31085361965389605141203345)
              ·
                refine ⟨23314021474042203855902509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31085361965389605141203345 23314021474042203855902509)
                ·
                  refine ⟨8742758052765826445963441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23314021474042203855902509 8742758052765826445963441)
                  ·
                    refine ⟨6557068539574369834472581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8742758052765826445963441 6557068539574369834472581)
                    ·
                      refine ⟨1229450351170194343963609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6557068539574369834472581 1229450351170194343963609)
                      ·
                        rfl

theorem cell23_2394346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2394346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394346 prefixEnd_2394346 := by exact prefixLift 2394346
  have htrace : WordTrace (prefixWord ++ tailWord_2394346) baseStart_2394346 baseEnd_2394346 := by
    simpa [prefixWord, tailWord_2394346, baseEnd_2394346] using wordTrace_append hprefix tailTrace_2394346
  have hstable : (prefixWord ++ tailWord_2394346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394346).length < 2 ^ (prefixWord ++ tailWord_2394346).sum := by decide
  have hdescent : baseEnd_2394346 < baseStart_2394346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394350 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_2394350 : Nat := 118140960795 + 2394350 * 2 ^ 59
def prefixEnd_2394350 : Nat := 4983230072969 + 3 ^ 40 * 2394350 * 2
def baseEnd_2394350 : Nat := 1229452405092812328313591

theorem tailTrace_2394350 : CollatzResearch.WordTrace tailWord_2394350 prefixEnd_2394350 1229452405092812328313591 := by
  unfold tailWord_2394350
  simp only [CollatzResearch.WordTrace]
  refine ⟨10916139859460793408641563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58219412583790898179421669 10916139859460793408641563)
  ·
    refine ⟨16374209789191190112962345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10916139859460793408641563 16374209789191190112962345)
    ·
      refine ⟨12280657341893392584721759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16374209789191190112962345 12280657341893392584721759)
      ·
        refine ⟨18420986012840088877082639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12280657341893392584721759 18420986012840088877082639)
        ·
          refine ⟨27631479019260133315623959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18420986012840088877082639 27631479019260133315623959)
          ·
            refine ⟨41447218528890199973435939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27631479019260133315623959 41447218528890199973435939)
            ·
              refine ⟨62170827793335299960153909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41447218528890199973435939 62170827793335299960153909)
              ·
                refine ⟨5828515105625184371264429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62170827793335299960153909 5828515105625184371264429)
                ·
                  refine ⟨2185693164609444139224161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5828515105625184371264429 2185693164609444139224161)
                  ·
                    refine ⟨1639269873457083104418121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2185693164609444139224161 1639269873457083104418121)
                    ·
                      refine ⟨1229452405092812328313591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639269873457083104418121 1229452405092812328313591)
                      ·
                        rfl

theorem cell23_2394350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_2394350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394350 prefixEnd_2394350 := by exact prefixLift 2394350
  have htrace : WordTrace (prefixWord ++ tailWord_2394350) baseStart_2394350 baseEnd_2394350 := by
    simpa [prefixWord, tailWord_2394350, baseEnd_2394350] using wordTrace_append hprefix tailTrace_2394350
  have hstable : (prefixWord ++ tailWord_2394350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394350).length < 2 ^ (prefixWord ++ tailWord_2394350).sum := by decide
  have hdescent : baseEnd_2394350 < baseStart_2394350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394370 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_2394370 : Nat := 118140960795 + 2394370 * 2 ^ 59
def prefixEnd_2394370 : Nat := 4983230072969 + 3 ^ 40 * 2394370 * 2
def baseEnd_2394370 : Nat := 1229462674705902250063499

theorem tailTrace_2394370 : CollatzResearch.WordTrace tailWord_2394370 prefixEnd_2394370 1229462674705902250063499 := by
  unfold tailWord_2394370
  simp only [CollatzResearch.WordTrace]
  refine ⟨21832462083903472671215141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58219898890409260456573709 21832462083903472671215141)
  ·
    refine ⟨4093586640731901125852839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21832462083903472671215141 4093586640731901125852839)
    ·
      refine ⟨6140379961097851688779259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4093586640731901125852839 6140379961097851688779259)
      ·
        refine ⟨9210569941646777533168889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6140379961097851688779259 9210569941646777533168889)
        ·
          refine ⟨6907927456235083149876667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9210569941646777533168889 6907927456235083149876667)
          ·
            refine ⟨10361891184352624724815001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6907927456235083149876667 10361891184352624724815001)
            ·
              refine ⟨7771418388264468543611251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10361891184352624724815001 7771418388264468543611251)
              ·
                refine ⟨11657127582396702815416877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7771418388264468543611251 11657127582396702815416877)
                ·
                  refine ⟨4371422843398763555781329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11657127582396702815416877 4371422843398763555781329)
                  ·
                    refine ⟨3278567132549072666835997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4371422843398763555781329 3278567132549072666835997)
                    ·
                      refine ⟨1229462674705902250063499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3278567132549072666835997 1229462674705902250063499)
                      ·
                        rfl

theorem cell23_2394370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_2394370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394370 prefixEnd_2394370 := by exact prefixLift 2394370
  have htrace : WordTrace (prefixWord ++ tailWord_2394370) baseStart_2394370 baseEnd_2394370 := by
    simpa [prefixWord, tailWord_2394370, baseEnd_2394370] using wordTrace_append hprefix tailTrace_2394370
  have hstable : (prefixWord ++ tailWord_2394370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394370).length < 2 ^ (prefixWord ++ tailWord_2394370).sum := by decide
  have hdescent : baseEnd_2394370 < baseStart_2394370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394400 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2394400 : Nat := 118140960795 + 2394400 * 2 ^ 59
def prefixEnd_2394400 : Nat := 4983230072969 + 3 ^ 40 * 2394400 * 2
def baseEnd_2394400 : Nat := 1229478079125537132688361

theorem tailTrace_2394400 : CollatzResearch.WordTrace tailWord_2394400 prefixEnd_2394400 1229478079125537132688361 := by
  unfold tailWord_2394400
  simp only [CollatzResearch.WordTrace]
  refine ⟨43665471262752602904226327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58220628350336803872301769 43665471262752602904226327)
  ·
    refine ⟨65498206894128904356339491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43665471262752602904226327 65498206894128904356339491)
    ·
      refine ⟨98247310341193356534509237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65498206894128904356339491 98247310341193356534509237)
      ·
        refine ⟨9210685344486877175110241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98247310341193356534509237 9210685344486877175110241)
        ·
          refine ⟨6908014008365157881332681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9210685344486877175110241 6908014008365157881332681)
          ·
            refine ⟨5181010506273868410999511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6908014008365157881332681 5181010506273868410999511)
            ·
              refine ⟨7771515759410802616499267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5181010506273868410999511 7771515759410802616499267)
              ·
                refine ⟨11657273639116203924748901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7771515759410802616499267 11657273639116203924748901)
                ·
                  refine ⟨2185738807334288235890419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11657273639116203924748901 2185738807334288235890419)
                  ·
                    refine ⟨3278608211001432353835629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2185738807334288235890419 3278608211001432353835629)
                    ·
                      refine ⟨1229478079125537132688361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3278608211001432353835629 1229478079125537132688361)
                      ·
                        rfl

theorem cell23_2394400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2394400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394400 prefixEnd_2394400 := by exact prefixLift 2394400
  have htrace : WordTrace (prefixWord ++ tailWord_2394400) baseStart_2394400 baseEnd_2394400 := by
    simpa [prefixWord, tailWord_2394400, baseEnd_2394400] using wordTrace_append hprefix tailTrace_2394400
  have hstable : (prefixWord ++ tailWord_2394400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394400).length < 2 ^ (prefixWord ++ tailWord_2394400).sum := by decide
  have hdescent : baseEnd_2394400 < baseStart_2394400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394414 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2394414 : Nat := 118140960795 + 2394414 * 2 ^ 59
def prefixEnd_2394414 : Nat := 4983230072969 + 3 ^ 40 * 2394414 * 2
def baseEnd_2394414 : Nat := 1229485267854700077913297

theorem tailTrace_2394414 : CollatzResearch.WordTrace tailWord_2394414 prefixEnd_2394414 1229485267854700077913297 := by
  unfold tailWord_2394414
  simp only [CollatzResearch.WordTrace]
  refine ⟨10916431643431810774932787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58220968764969657466308197 10916431643431810774932787)
  ·
    refine ⟨16374647465147716162399181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10916431643431810774932787 16374647465147716162399181)
    ·
      refine ⟨6140492799430393560899693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16374647465147716162399181 6140492799430393560899693)
      ·
        refine ⟨2302684799786397585337385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6140492799430393560899693 2302684799786397585337385)
        ·
          refine ⟨1727013599839798189003039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2302684799786397585337385 1727013599839798189003039)
          ·
            refine ⟨2590520399759697283504559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727013599839798189003039 2590520399759697283504559)
            ·
              refine ⟨3885780599639545925256839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590520399759697283504559 3885780599639545925256839)
              ·
                refine ⟨5828670899459318887885259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3885780599639545925256839 5828670899459318887885259)
                ·
                  refine ⟨8743006349188978331827889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5828670899459318887885259 8743006349188978331827889)
                  ·
                    refine ⟨6557254761891733748870917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8743006349188978331827889 6557254761891733748870917)
                    ·
                      refine ⟨1229485267854700077913297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6557254761891733748870917 1229485267854700077913297)
                      ·
                        rfl

theorem cell23_2394414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2394414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394414 prefixEnd_2394414 := by exact prefixLift 2394414
  have htrace : WordTrace (prefixWord ++ tailWord_2394414) baseStart_2394414 baseEnd_2394414 := by
    simpa [prefixWord, tailWord_2394414, baseEnd_2394414] using wordTrace_append hprefix tailTrace_2394414
  have hstable : (prefixWord ++ tailWord_2394414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394414).length < 2 ^ (prefixWord ++ tailWord_2394414).sum := by decide
  have hdescent : baseEnd_2394414 < baseStart_2394414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394417 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 1, 3, 3]
def baseStart_2394417 : Nat := 118140960795 + 2394417 * 2 ^ 59
def prefixEnd_2394417 : Nat := 4983230072969 + 3 ^ 40 * 2394417 * 2
def baseEnd_2394417 : Nat := 1229486808296663566175783

theorem tailTrace_2394417 : CollatzResearch.WordTrace tailWord_2394417 prefixEnd_2394417 1229486808296663566175783 := by
  unfold tailWord_2394417
  simp only [CollatzResearch.WordTrace]
  refine ⟨87331562566443617711821505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58221041710962411807881003 87331562566443617711821505)
  ·
    refine ⟨65498671924832713283866129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87331562566443617711821505 65498671924832713283866129)
    ·
      refine ⟨49124003943624534962899597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65498671924832713283866129 49124003943624534962899597)
      ·
        refine ⟨18421501478859200611087349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49124003943624534962899597 18421501478859200611087349)
        ·
          refine ⟨1727015763643050057289439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18421501478859200611087349 1727015763643050057289439)
          ·
            refine ⟨2590523645464575085934159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727015763643050057289439 2590523645464575085934159)
            ·
              refine ⟨3885785468196862628901239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590523645464575085934159 3885785468196862628901239)
              ·
                refine ⟨5828678202295293943351859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3885785468196862628901239 5828678202295293943351859)
                ·
                  refine ⟨8743017303442940915027789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5828678202295293943351859 8743017303442940915027789)
                  ·
                    refine ⟨3278631488791102843135421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8743017303442940915027789 3278631488791102843135421)
                    ·
                      refine ⟨1229486808296663566175783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3278631488791102843135421 1229486808296663566175783)
                      ·
                        rfl

theorem cell23_2394417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_2394417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394417 prefixEnd_2394417 := by exact prefixLift 2394417
  have htrace : WordTrace (prefixWord ++ tailWord_2394417) baseStart_2394417 baseEnd_2394417 := by
    simpa [prefixWord, tailWord_2394417, baseEnd_2394417] using wordTrace_append hprefix tailTrace_2394417
  have hstable : (prefixWord ++ tailWord_2394417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394417).length < 2 ^ (prefixWord ++ tailWord_2394417).sum := by decide
  have hdescent : baseEnd_2394417 < baseStart_2394417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394440 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 4, 2, 2]
def baseStart_2394440 : Nat := 118140960795 + 2394440 * 2 ^ 59
def prefixEnd_2394440 : Nat := 4983230072969 + 3 ^ 40 * 2394440 * 2
def baseEnd_2394440 : Nat := 1229498618351716976188177

theorem tailTrace_2394440 : CollatzResearch.WordTrace tailWord_2394440 prefixEnd_2394440 1229498618351716976188177 := by
  unfold tailWord_2394440
  simp only [CollatzResearch.WordTrace]
  refine ⟨43666200722680146319954387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58221600963573528426605849 43666200722680146319954387)
  ·
    refine ⟨65499301084020219479931581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43666200722680146319954387 65499301084020219479931581)
    ·
      refine ⟨24562237906507582304974343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65499301084020219479931581 24562237906507582304974343)
      ·
        refine ⟨36843356859761373457461515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24562237906507582304974343 36843356859761373457461515)
        ·
          refine ⟨55265035289642060186192273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36843356859761373457461515 55265035289642060186192273)
          ·
            refine ⟨41448776467231545139644205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55265035289642060186192273 41448776467231545139644205)
            ·
              refine ⟨15543291175211829427366577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41448776467231545139644205 15543291175211829427366577)
              ·
                refine ⟨11657468381408872070524933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15543291175211829427366577 11657468381408872070524933)
                ·
                  refine ⟨2185775321514163513223425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11657468381408872070524933 2185775321514163513223425)
                  ·
                    refine ⟨1639331491135622634917569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2185775321514163513223425 1639331491135622634917569)
                    ·
                      refine ⟨1229498618351716976188177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639331491135622634917569 1229498618351716976188177)
                      ·
                        rfl

theorem cell23_2394440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_2394440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394440 prefixEnd_2394440 := by exact prefixLift 2394440
  have htrace : WordTrace (prefixWord ++ tailWord_2394440) baseStart_2394440 baseEnd_2394440 := by
    simpa [prefixWord, tailWord_2394440, baseEnd_2394440] using wordTrace_append hprefix tailTrace_2394440
  have hstable : (prefixWord ++ tailWord_2394440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394440).length < 2 ^ (prefixWord ++ tailWord_2394440).sum := by decide
  have hdescent : baseEnd_2394440 < baseStart_2394440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394463 : List Nat := [1, 1, 2, 3, 1, 2, 2, 6, 5]
def baseStart_2394463 : Nat := 118140960795 + 2394463 * 2 ^ 59
def prefixEnd_2394463 : Nat := 4983230072969 + 3 ^ 40 * 2394463 * 2
def baseEnd_2394463 : Nat := 136612269822974487355619

theorem tailTrace_2394463 : CollatzResearch.WordTrace tailWord_2394463 prefixEnd_2394463 136612269822974487355619 := by
  unfold tailWord_2394463
  simp only [CollatzResearch.WordTrace]
  refine ⟨87333240324276967567996043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58222160216184645045330695 87333240324276967567996043)
  ·
    refine ⟨130999860486415451351994065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87333240324276967567996043 130999860486415451351994065)
    ·
      refine ⟨98249895364811588513995549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130999860486415451351994065 98249895364811588513995549)
      ·
        refine ⟨36843710761804345692748331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98249895364811588513995549 36843710761804345692748331)
        ·
          refine ⟨55265566142706518539122497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36843710761804345692748331 55265566142706518539122497)
          ·
            refine ⟨41449174607029888904341873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55265566142706518539122497 41449174607029888904341873)
            ·
              refine ⟨31086880955272416678256405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41449174607029888904341873 31086880955272416678256405)
              ·
                refine ⟨1457197544778394531793269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31086880955272416678256405 1457197544778394531793269)
                ·
                  refine ⟨136612269822974487355619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1457197544778394531793269 136612269822974487355619)
                  ·
                    rfl

theorem cell23_2394463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 5].length) (baseStart_2394463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394463 prefixEnd_2394463 := by exact prefixLift 2394463
  have htrace : WordTrace (prefixWord ++ tailWord_2394463) baseStart_2394463 baseEnd_2394463 := by
    simpa [prefixWord, tailWord_2394463, baseEnd_2394463] using wordTrace_append hprefix tailTrace_2394463
  have hstable : (prefixWord ++ tailWord_2394463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394463).length < 2 ^ (prefixWord ++ tailWord_2394463).sum := by decide
  have hdescent : baseEnd_2394463 < baseStart_2394463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394474 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_2394474 : Nat := 118140960795 + 2394474 * 2 ^ 59
def prefixEnd_2394474 : Nat := 4983230072969 + 3 ^ 40 * 2394474 * 2
def baseEnd_2394474 : Nat := 1229516076693969843163021

theorem tailTrace_2394474 : CollatzResearch.WordTrace tailWord_2394474 prefixEnd_2394474 1229516076693969843163021 := by
  unfold tailWord_2394474
  simp only [CollatzResearch.WordTrace]
  refine ⟨21833410381809279111661619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58222427684824744297764317 21833410381809279111661619)
  ·
    refine ⟨32750115572713918667492429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21833410381809279111661619 32750115572713918667492429)
    ·
      refine ⟨12281293339767719500309661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32750115572713918667492429 12281293339767719500309661)
      ·
        refine ⟨4605485002412894812616123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12281293339767719500309661 4605485002412894812616123)
        ·
          refine ⟨6908227503619342218924185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4605485002412894812616123 6908227503619342218924185)
          ·
            refine ⟨5181170627714506664193139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6908227503619342218924185 5181170627714506664193139)
            ·
              refine ⟨7771755941571759996289709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5181170627714506664193139 7771755941571759996289709)
              ·
                refine ⟨2914408478089409998608641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7771755941571759996289709 2914408478089409998608641)
                ·
                  refine ⟨2185806358567057498956481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2914408478089409998608641 2185806358567057498956481)
                  ·
                    refine ⟨1639354768925293124217361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2185806358567057498956481 1639354768925293124217361)
                    ·
                      refine ⟨1229516076693969843163021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639354768925293124217361 1229516076693969843163021)
                      ·
                        rfl

theorem cell23_2394474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_2394474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394474 prefixEnd_2394474 := by exact prefixLift 2394474
  have htrace : WordTrace (prefixWord ++ tailWord_2394474) baseStart_2394474 baseEnd_2394474 := by
    simpa [prefixWord, tailWord_2394474, baseEnd_2394474] using wordTrace_append hprefix tailTrace_2394474
  have hstable : (prefixWord ++ tailWord_2394474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394474).length < 2 ^ (prefixWord ++ tailWord_2394474).sum := by decide
  have hdescent : baseEnd_2394474 < baseStart_2394474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394483 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 2, 5, 2]
def baseStart_2394483 : Nat := 118140960795 + 2394483 * 2 ^ 59
def prefixEnd_2394483 : Nat := 4983230072969 + 3 ^ 40 * 2394483 * 2
def baseEnd_2394483 : Nat := 1229520698019860307950479

theorem tailTrace_2394483 : CollatzResearch.WordTrace tailWord_2394483 prefixEnd_2394483 1229520698019860307950479 := by
  unfold tailWord_2394483
  simp only [CollatzResearch.WordTrace]
  refine ⟨87333969784204510983724103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58222646522803007322482735 87333969784204510983724103)
  ·
    refine ⟨131000954676306766475586155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87333969784204510983724103 131000954676306766475586155)
    ·
      refine ⟨196501432014460149713379233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131000954676306766475586155 196501432014460149713379233)
      ·
        refine ⟨147376074010845112285034425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196501432014460149713379233 147376074010845112285034425)
        ·
          refine ⟨110532055508133834213775819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147376074010845112285034425 110532055508133834213775819)
          ·
            refine ⟨165798083262200751320663729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110532055508133834213775819 165798083262200751320663729)
            ·
              refine ⟨124348562446650563490497797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165798083262200751320663729 124348562446650563490497797)
              ·
                refine ⟨23315355458746980654468337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124348562446650563490497797 23315355458746980654468337)
                ·
                  refine ⟨17486516594060235490851253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23315355458746980654468337 17486516594060235490851253)
                  ·
                    refine ⟨1639360930693147077267305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17486516594060235490851253 1639360930693147077267305)
                    ·
                      refine ⟨1229520698019860307950479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1639360930693147077267305 1229520698019860307950479)
                      ·
                        rfl

theorem cell23_2394483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 5, 2].length) (baseStart_2394483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394483 prefixEnd_2394483 := by exact prefixLift 2394483
  have htrace : WordTrace (prefixWord ++ tailWord_2394483) baseStart_2394483 baseEnd_2394483 := by
    simpa [prefixWord, tailWord_2394483, baseEnd_2394483] using wordTrace_append hprefix tailTrace_2394483
  have hstable : (prefixWord ++ tailWord_2394483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394483).length < 2 ^ (prefixWord ++ tailWord_2394483).sum := by decide
  have hdescent : baseEnd_2394483 < baseStart_2394483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394493 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_2394493 : Nat := 118140960795 + 2394493 * 2 ^ 59
def prefixEnd_2394493 : Nat := 4983230072969 + 3 ^ 40 * 2394493 * 2
def baseEnd_2394493 : Nat := 409841944275468422941811

theorem tailTrace_2394493 : CollatzResearch.WordTrace tailWord_2394493 prefixEnd_2394493 409841944275468422941811 := by
  unfold tailWord_2394493
  simp only [CollatzResearch.WordTrace]
  refine ⟨87334334514168282691588133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58222889676112188461058755 87334334514168282691588133)
  ·
    refine ⟨16375187721406553004672775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87334334514168282691588133 16375187721406553004672775)
    ·
      refine ⟨24562781582109829507009163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16375187721406553004672775 24562781582109829507009163)
      ·
        refine ⟨36844172373164744260513745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24562781582109829507009163 36844172373164744260513745)
        ·
          refine ⟨27633129279873558195385309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36844172373164744260513745 27633129279873558195385309)
          ·
            refine ⟨10362423479952584323269491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27633129279873558195385309 10362423479952584323269491)
            ·
              refine ⟨15543635219928876484904237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10362423479952584323269491 15543635219928876484904237)
              ·
                refine ⟨5828863207473328681839089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15543635219928876484904237 5828863207473328681839089)
                ·
                  refine ⟨4371647405604996511379317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5828863207473328681839089 4371647405604996511379317)
                  ·
                    refine ⟨409841944275468422941811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4371647405604996511379317 409841944275468422941811)
                    ·
                      rfl

theorem cell23_2394493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_2394493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394493 prefixEnd_2394493 := by exact prefixLift 2394493
  have htrace : WordTrace (prefixWord ++ tailWord_2394493) baseStart_2394493 baseEnd_2394493 := by
    simpa [prefixWord, tailWord_2394493, baseEnd_2394493] using wordTrace_append hprefix tailTrace_2394493
  have hstable : (prefixWord ++ tailWord_2394493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394493).length < 2 ^ (prefixWord ++ tailWord_2394493).sum := by decide
  have hdescent : baseEnd_2394493 < baseStart_2394493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394510 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_2394510 : Nat := 118140960795 + 2394510 * 2 ^ 59
def prefixEnd_2394510 : Nat := 4983230072969 + 3 ^ 40 * 2394510 * 2
def baseEnd_2394510 : Nat := 409844853999177234104285

theorem tailTrace_2394510 : CollatzResearch.WordTrace tailWord_2394510 prefixEnd_2394510 409844853999177234104285 := by
  unfold tailWord_2394510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10916869319388336824369623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58223303036737796396637989 10916869319388336824369623)
  ·
    refine ⟨16375303979082505236554435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10916869319388336824369623 16375303979082505236554435)
    ·
      refine ⟨24562955968623757854831653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16375303979082505236554435 24562955968623757854831653)
      ·
        refine ⟨4605554244116954597780935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24562955968623757854831653 4605554244116954597780935)
        ·
          refine ⟨6908331366175431896671403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4605554244116954597780935 6908331366175431896671403)
          ·
            refine ⟨10362497049263147845007105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6908331366175431896671403 10362497049263147845007105)
            ·
              refine ⟨7771872786947360883755329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10362497049263147845007105 7771872786947360883755329)
              ·
                refine ⟨5828904590210520662816497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7771872786947360883755329 5828904590210520662816497)
                ·
                  refine ⟨4371678442657890497112373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5828904590210520662816497 4371678442657890497112373)
                  ·
                    refine ⟨409844853999177234104285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4371678442657890497112373 409844853999177234104285)
                    ·
                      rfl

theorem cell23_2394510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_2394510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394510 prefixEnd_2394510 := by exact prefixLift 2394510
  have htrace : WordTrace (prefixWord ++ tailWord_2394510) baseStart_2394510 baseEnd_2394510 := by
    simpa [prefixWord, tailWord_2394510, baseEnd_2394510] using wordTrace_append hprefix tailTrace_2394510
  have hstable : (prefixWord ++ tailWord_2394510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394510).length < 2 ^ (prefixWord ++ tailWord_2394510).sum := by decide
  have hdescent : baseEnd_2394510 < baseStart_2394510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394533 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 1, 4, 3]
def baseStart_2394533 : Nat := 118140960795 + 2394533 * 2 ^ 59
def prefixEnd_2394533 : Nat := 4983230072969 + 3 ^ 40 * 2394533 * 2
def baseEnd_2394533 : Nat := 1229546372052585112325249

theorem tailTrace_2394533 : CollatzResearch.WordTrace tailWord_2394533 prefixEnd_2394533 1229546372052585112325249 := by
  unfold tailWord_2394533
  simp only [CollatzResearch.WordTrace]
  refine ⟨87335793434023369523044253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58223862289348913015362835 87335793434023369523044253)
  ·
    refine ⟨32750922537758763571141595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87335793434023369523044253 32750922537758763571141595)
    ·
      refine ⟨49126383806638145356712393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32750922537758763571141595 49126383806638145356712393)
      ·
        refine ⟨36844787854978609017534295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49126383806638145356712393 36844787854978609017534295)
        ·
          refine ⟨55267181782467913526301443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36844787854978609017534295 55267181782467913526301443)
          ·
            refine ⟨82900772673701870289452165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55267181782467913526301443 82900772673701870289452165)
            ·
              refine ⟨15543894876319100679272281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82900772673701870289452165 15543894876319100679272281)
              ·
                refine ⟨11657921157239325509454211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15543894876319100679272281 11657921157239325509454211)
                ·
                  refine ⟨17486881735858988264181317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11657921157239325509454211 17486881735858988264181317)
                  ·
                    refine ⟨3278790325473560299533997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17486881735858988264181317 3278790325473560299533997)
                    ·
                      refine ⟨1229546372052585112325249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3278790325473560299533997 1229546372052585112325249)
                      ·
                        rfl

theorem cell23_2394533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_2394533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394533 prefixEnd_2394533 := by exact prefixLift 2394533
  have htrace : WordTrace (prefixWord ++ tailWord_2394533) baseStart_2394533 baseEnd_2394533 := by
    simpa [prefixWord, tailWord_2394533, baseEnd_2394533] using wordTrace_append hprefix tailTrace_2394533
  have hstable : (prefixWord ++ tailWord_2394533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394533).length < 2 ^ (prefixWord ++ tailWord_2394533).sum := by decide
  have hdescent : baseEnd_2394533 < baseStart_2394533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394557 : List Nat := [1, 4, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_2394557 : Nat := 118140960795 + 2394557 * 2 ^ 59
def prefixEnd_2394557 : Nat := 4983230072969 + 3 ^ 40 * 2394557 * 2
def baseEnd_2394557 : Nat := 409852898529431006141713

theorem tailTrace_2394557 : CollatzResearch.WordTrace tailWord_2394557 prefixEnd_2394557 409852898529431006141713 := by
  unfold tailWord_2394557
  simp only [CollatzResearch.WordTrace]
  refine ⟨87336668785936421621917925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58224445857290947747945283 87336668785936421621917925)
  ·
    refine ⟨16375625397363079054109611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87336668785936421621917925 16375625397363079054109611)
    ·
      refine ⟨24563438096044618581164417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16375625397363079054109611 24563438096044618581164417)
      ·
        refine ⟨18422578572033463935873313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24563438096044618581164417 18422578572033463935873313)
        ·
          refine ⟨13816933929025097951904985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18422578572033463935873313 13816933929025097951904985)
          ·
            refine ⟨10362700446768823463928739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13816933929025097951904985 10362700446768823463928739)
            ·
              refine ⟨15544050670153235195893109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10362700446768823463928739 15544050670153235195893109)
              ·
                refine ⟨1457254750326865799614979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15544050670153235195893109 1457254750326865799614979)
                ·
                  refine ⟨2185882125490298699422469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457254750326865799614979 2185882125490298699422469)
                  ·
                    refine ⟨409852898529431006141713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2185882125490298699422469 409852898529431006141713)
                    ·
                      rfl

theorem cell23_2394557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_2394557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394557 prefixEnd_2394557 := by exact prefixLift 2394557
  have htrace : WordTrace (prefixWord ++ tailWord_2394557) baseStart_2394557 baseEnd_2394557 := by
    simpa [prefixWord, tailWord_2394557, baseEnd_2394557] using wordTrace_append hprefix tailTrace_2394557
  have hstable : (prefixWord ++ tailWord_2394557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394557).length < 2 ^ (prefixWord ++ tailWord_2394557).sum := by decide
  have hdescent : baseEnd_2394557 < baseStart_2394557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394600 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 1, 5]
def baseStart_2394600 : Nat := 118140960795 + 2394600 * 2 ^ 59
def prefixEnd_2394600 : Nat := 4983230072969 + 3 ^ 40 * 2394600 * 2
def baseEnd_2394600 : Nat := 409860258418812116729147

theorem tailTrace_2394600 : CollatzResearch.WordTrace tailWord_2394600 prefixEnd_2394600 409860258418812116729147 := by
  unfold tailWord_2394600
  simp only [CollatzResearch.WordTrace]
  refine ⟨43669118562390319982866627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58225491416520426643822169 43669118562390319982866627)
  ·
    refine ⟨65503677843585479974299941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43669118562390319982866627 65503677843585479974299941)
    ·
      refine ⟨12281939595672277495181239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65503677843585479974299941 12281939595672277495181239)
      ·
        refine ⟨18422909393508416242771859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12281939595672277495181239 18422909393508416242771859)
        ·
          refine ⟨27634364090262624364157789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18422909393508416242771859 27634364090262624364157789)
          ·
            refine ⟨10362886533848484136559171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27634364090262624364157789 10362886533848484136559171)
            ·
              refine ⟨15544329800772726204838757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10362886533848484136559171 15544329800772726204838757)
              ·
                refine ⟨2914561837644886163407267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15544329800772726204838757 2914561837644886163407267)
                ·
                  refine ⟨4371842756467329245110901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2914561837644886163407267 4371842756467329245110901)
                  ·
                    refine ⟨409860258418812116729147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4371842756467329245110901 409860258418812116729147)
                    ·
                      rfl

theorem cell23_2394600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_2394600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394600 prefixEnd_2394600 := by exact prefixLift 2394600
  have htrace : WordTrace (prefixWord ++ tailWord_2394600) baseStart_2394600 baseEnd_2394600 := by
    simpa [prefixWord, tailWord_2394600, baseEnd_2394600] using wordTrace_append hprefix tailTrace_2394600
  have hstable : (prefixWord ++ tailWord_2394600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394600).length < 2 ^ (prefixWord ++ tailWord_2394600).sum := by decide
  have hdescent : baseEnd_2394600 < baseStart_2394600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394631 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 3, 1, 3]
def baseStart_2394631 : Nat := 118140960795 + 2394631 * 2 ^ 59
def prefixEnd_2394631 : Nat := 4983230072969 + 3 ^ 40 * 2394631 * 2
def baseEnd_2394631 : Nat := 1229596693156725728899799

theorem tailTrace_2394631 : CollatzResearch.WordTrace tailWord_2394631 prefixEnd_2394631 1229596693156725728899799 := by
  unfold tailWord_2394631
  simp only [CollatzResearch.WordTrace]
  refine ⟨87339367787668332260111747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58226245191778888173407831 87339367787668332260111747)
  ·
    refine ⟨131009051681502498390167621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87339367787668332260111747 131009051681502498390167621)
    ·
      refine ⟨24564197190281718448156429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131009051681502498390167621 24564197190281718448156429)
      ·
        refine ⟨9211573946355644418058661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24564197190281718448156429 9211573946355644418058661)
        ·
          refine ⟨1727170114941683328385999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9211573946355644418058661 1727170114941683328385999)
          ·
            refine ⟨2590755172412524992578999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727170114941683328385999 2590755172412524992578999)
            ·
              refine ⟨3886132758618787488868499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590755172412524992578999 3886132758618787488868499)
              ·
                refine ⟨5829199137928181233302749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3886132758618787488868499 5829199137928181233302749)
                ·
                  refine ⟨2185949676723067962488531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5829199137928181233302749 2185949676723067962488531)
                  ·
                    refine ⟨3278924515084601943732797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2185949676723067962488531 3278924515084601943732797)
                    ·
                      refine ⟨1229596693156725728899799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3278924515084601943732797 1229596693156725728899799)
                      ·
                        rfl

theorem cell23_2394631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_2394631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394631 prefixEnd_2394631 := by exact prefixLift 2394631
  have htrace : WordTrace (prefixWord ++ tailWord_2394631) baseStart_2394631 baseEnd_2394631 := by
    simpa [prefixWord, tailWord_2394631, baseEnd_2394631] using wordTrace_append hprefix tailTrace_2394631
  have hstable : (prefixWord ++ tailWord_2394631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394631).length < 2 ^ (prefixWord ++ tailWord_2394631).sum := by decide
  have hdescent : baseEnd_2394631 < baseStart_2394631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394633 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 4]
def baseStart_2394633 : Nat := 118140960795 + 2394633 * 2 ^ 59
def prefixEnd_2394633 : Nat := 4983230072969 + 3 ^ 40 * 2394633 * 2
def baseEnd_2394633 : Nat := 1229597720118034721074789

theorem tailTrace_2394633 : CollatzResearch.WordTrace tailWord_2394633 prefixEnd_2394633 1229597720118034721074789 := by
  unfold tailWord_2394633
  simp only [CollatzResearch.WordTrace]
  refine ⟨87339440733661086601684553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58226293822440724401123035 87339440733661086601684553)
  ·
    refine ⟨65504580550245814951263415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87339440733661086601684553 65504580550245814951263415)
    ·
      refine ⟨98256870825368722426895123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65504580550245814951263415 98256870825368722426895123)
      ·
        refine ⟨147385306238053083640342685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98256870825368722426895123 147385306238053083640342685)
        ·
          refine ⟨55269489839269906365128507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147385306238053083640342685 55269489839269906365128507)
          ·
            refine ⟨82904234758904859547692761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55269489839269906365128507 82904234758904859547692761)
            ·
              refine ⟨62178176069178644660769571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82904234758904859547692761 62178176069178644660769571)
              ·
                refine ⟨93267264103767966991154357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62178176069178644660769571 93267264103767966991154357)
                ·
                  refine ⟨8743806009728246905420721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93267264103767966991154357 8743806009728246905420721)
                  ·
                    refine ⟨6557854507296185179065541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8743806009728246905420721 6557854507296185179065541)
                    ·
                      refine ⟨1229597720118034721074789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6557854507296185179065541 1229597720118034721074789)
                      ·
                        rfl

theorem cell23_2394633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_2394633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394633 prefixEnd_2394633 := by exact prefixLift 2394633
  have htrace : WordTrace (prefixWord ++ tailWord_2394633) baseStart_2394633 baseEnd_2394633 := by
    simpa [prefixWord, tailWord_2394633, baseEnd_2394633] using wordTrace_append hprefix tailTrace_2394633
  have hstable : (prefixWord ++ tailWord_2394633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394633).length < 2 ^ (prefixWord ++ tailWord_2394633).sum := by decide
  have hdescent : baseEnd_2394633 < baseStart_2394633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394643 : List Nat := [1, 1, 1, 2, 1, 5, 4, 8]
def baseStart_2394643 : Nat := 118140960795 + 2394643 * 2 ^ 59
def prefixEnd_2394643 : Nat := 4983230072969 + 3 ^ 40 * 2394643 * 2
def baseEnd_2394643 : Nat := 45540846478688136368509

theorem tailTrace_2394643 : CollatzResearch.WordTrace tailWord_2394643 prefixEnd_2394643 45540846478688136368509 := by
  unfold tailWord_2394643
  simp only [CollatzResearch.WordTrace]
  refine ⟨87339805463624858309548583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58226536975749905539699055 87339805463624858309548583)
  ·
    refine ⟨131009708195437287464322875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87339805463624858309548583 131009708195437287464322875)
    ·
      refine ⟨196514562293155931196484313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131009708195437287464322875 196514562293155931196484313)
      ·
        refine ⟨147385921719866948397363235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196514562293155931196484313 147385921719866948397363235)
        ·
          refine ⟨221078882579800422596044853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147385921719866948397363235 221078882579800422596044853)
          ·
            refine ⟨20726145241856289618379205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221078882579800422596044853 20726145241856289618379205)
            ·
              refine ⟨3886152232848054303446101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20726145241856289618379205 3886152232848054303446101)
              ·
                refine ⟨45540846478688136368509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3886152232848054303446101 45540846478688136368509)
                ·
                  rfl

theorem cell23_2394643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 8].length) (baseStart_2394643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394643 prefixEnd_2394643 := by exact prefixLift 2394643
  have htrace : WordTrace (prefixWord ++ tailWord_2394643) baseStart_2394643 baseEnd_2394643 := by
    simpa [prefixWord, tailWord_2394643, baseEnd_2394643] using wordTrace_append hprefix tailTrace_2394643
  have hstable : (prefixWord ++ tailWord_2394643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394643).length < 2 ^ (prefixWord ++ tailWord_2394643).sum := by decide
  have hdescent : baseEnd_2394643 < baseStart_2394643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394694 : List Nat := [6, 1, 1, 1, 2, 3, 1, 8]
def baseStart_2394694 : Nat := 118140960795 + 2394694 * 2 ^ 59
def prefixEnd_2394694 : Nat := 4983230072969 + 3 ^ 40 * 2394694 * 2
def baseEnd_2394694 : Nat := 45541816386591073422667

theorem tailTrace_2394694 : CollatzResearch.WordTrace tailWord_2394694 prefixEnd_2394694 45541816386591073422667 := by
  unfold tailWord_2394694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729427049576252938114223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58227777057626729346436757 2729427049576252938114223)
  ·
    refine ⟨4094140574364379407171335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2729427049576252938114223 4094140574364379407171335)
    ·
      refine ⟨6141210861546569110757003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4094140574364379407171335 6141210861546569110757003)
      ·
        refine ⟨9211816292319853666135505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6141210861546569110757003 9211816292319853666135505)
        ·
          refine ⟨6908862219239890249601629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9211816292319853666135505 6908862219239890249601629)
          ·
            refine ⟨2590823332214958843600611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6908862219239890249601629 2590823332214958843600611)
            ·
              refine ⟨3886234998322438265400917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590823332214958843600611 3886234998322438265400917)
              ·
                refine ⟨45541816386591073422667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3886234998322438265400917 45541816386591073422667)
                ·
                  rfl

theorem cell23_2394694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_2394694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394694 prefixEnd_2394694 := by exact prefixLift 2394694
  have htrace : WordTrace (prefixWord ++ tailWord_2394694) baseStart_2394694 baseEnd_2394694 := by
    simpa [prefixWord, tailWord_2394694, baseEnd_2394694] using wordTrace_append hprefix tailTrace_2394694
  have hstable : (prefixWord ++ tailWord_2394694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394694).length < 2 ^ (prefixWord ++ tailWord_2394694).sum := by decide
  have hdescent : baseEnd_2394694 < baseStart_2394694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394703 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 1, 8]
def baseStart_2394703 : Nat := 118140960795 + 2394703 * 2 ^ 59
def prefixEnd_2394703 : Nat := 4983230072969 + 3 ^ 40 * 2394703 * 2
def baseEnd_2394703 : Nat := 409877887921283149066489

theorem tailTrace_2394703 : CollatzResearch.WordTrace tailWord_2394703 prefixEnd_2394703 409877887921283149066489 := by
  unfold tailWord_2394703
  simp only [CollatzResearch.WordTrace]
  refine ⟨87341993843407488556732763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58227995895604992371155175 87341993843407488556732763)
  ·
    refine ⟨131012990765111232835099145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87341993843407488556732763 131012990765111232835099145)
    ·
      refine ⟨98259743073833424626324359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131012990765111232835099145 98259743073833424626324359)
      ·
        refine ⟨147389614610750136939486539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98259743073833424626324359 147389614610750136939486539)
        ·
          refine ⟨221084421916125205409229809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147389614610750136939486539 221084421916125205409229809)
          ·
            refine ⟨165813316437093904056922357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221084421916125205409229809 165813316437093904056922357)
            ·
              refine ⟨15544998415977553505336471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165813316437093904056922357 15544998415977553505336471)
              ·
                refine ⟨23317497623966330258004707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15544998415977553505336471 23317497623966330258004707)
                ·
                  refine ⟨34976246435949495387007061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23317497623966330258004707 34976246435949495387007061)
                  ·
                    refine ⟨409877887921283149066489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34976246435949495387007061 409877887921283149066489)
                    ·
                      rfl

theorem cell23_2394703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_2394703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394703 prefixEnd_2394703 := by exact prefixLift 2394703
  have htrace : WordTrace (prefixWord ++ tailWord_2394703) baseStart_2394703 baseEnd_2394703 := by
    simpa [prefixWord, tailWord_2394703, baseEnd_2394703] using wordTrace_append hprefix tailTrace_2394703
  have hstable : (prefixWord ++ tailWord_2394703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394703).length < 2 ^ (prefixWord ++ tailWord_2394703).sum := by decide
  have hdescent : baseEnd_2394703 < baseStart_2394703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394730 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2394730 : Nat := 118140960795 + 2394730 * 2 ^ 59
def prefixEnd_2394730 : Nat := 4983230072969 + 3 ^ 40 * 2394730 * 2
def baseEnd_2394730 : Nat := 1229647527741520841561843

theorem tailTrace_2394730 : CollatzResearch.WordTrace tailWord_2394730 prefixEnd_2394730 1229647527741520841561843 := by
  unfold tailWord_2394730
  simp only [CollatzResearch.WordTrace]
  refine ⟨21835744653577418041991411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58228652409539781445310429 21835744653577418041991411)
  ·
    refine ⟨32753616980366127062987117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21835744653577418041991411 32753616980366127062987117)
    ·
      refine ⟨12282606367637297648620169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32753616980366127062987117 12282606367637297648620169)
      ·
        refine ⟨9211954775727973236465127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12282606367637297648620169 9211954775727973236465127)
        ·
          refine ⟨13817932163591959854697691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9211954775727973236465127 13817932163591959854697691)
          ·
            refine ⟨20726898245387939782046537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13817932163591959854697691 20726898245387939782046537)
            ·
              refine ⟨15545173684040954836534903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20726898245387939782046537 15545173684040954836534903)
              ·
                refine ⟨23317760526061432254802355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15545173684040954836534903 23317760526061432254802355)
                ·
                  refine ⟨34976640789092148382203533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23317760526061432254802355 34976640789092148382203533)
                  ·
                    refine ⟨13116240295909555643326325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34976640789092148382203533 13116240295909555643326325)
                    ·
                      refine ⟨1229647527741520841561843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13116240295909555643326325 1229647527741520841561843)
                      ·
                        rfl

theorem cell23_2394730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2394730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394730 prefixEnd_2394730 := by exact prefixLift 2394730
  have htrace : WordTrace (prefixWord ++ tailWord_2394730) baseStart_2394730 baseEnd_2394730 := by
    simpa [prefixWord, tailWord_2394730, baseEnd_2394730] using wordTrace_append hprefix tailTrace_2394730
  have hstable : (prefixWord ++ tailWord_2394730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394730).length < 2 ^ (prefixWord ++ tailWord_2394730).sum := by decide
  have hdescent : baseEnd_2394730 < baseStart_2394730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394738 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 2, 1, 3]
def baseStart_2394738 : Nat := 118140960795 + 2394738 * 2 ^ 59
def prefixEnd_2394738 : Nat := 4983230072969 + 3 ^ 40 * 2394738 * 2
def baseEnd_2394738 : Nat := 1229651635586756810261807

theorem tailTrace_2394738 : CollatzResearch.WordTrace tailWord_2394738 prefixEnd_2394738 1229651635586756810261807 := by
  unfold tailWord_2394738
  simp only [CollatzResearch.WordTrace]
  refine ⟨21835817599570172383564217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58228846932187126356171245 21835817599570172383564217)
  ·
    refine ⟨16376863199677629287673163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21835817599570172383564217 16376863199677629287673163)
    ·
      refine ⟨24565294799516443931509745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16376863199677629287673163 24565294799516443931509745)
      ·
        refine ⟨18423971099637332948632309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24565294799516443931509745 18423971099637332948632309)
        ·
          refine ⟨1727247290590999963934279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18423971099637332948632309 1727247290590999963934279)
          ·
            refine ⟨2590870935886499945901419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727247290590999963934279 2590870935886499945901419)
            ·
              refine ⟨3886306403829749918852129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590870935886499945901419 3886306403829749918852129)
              ·
                refine ⟨2914729802872312439139097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3886306403829749918852129 2914729802872312439139097)
                ·
                  refine ⟨2186047352154234329354323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2914729802872312439139097 2186047352154234329354323)
                  ·
                    refine ⟨3279071028231351494031485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2186047352154234329354323 3279071028231351494031485)
                    ·
                      refine ⟨1229651635586756810261807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3279071028231351494031485 1229651635586756810261807)
                      ·
                        rfl

theorem cell23_2394738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_2394738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394738 prefixEnd_2394738 := by exact prefixLift 2394738
  have htrace : WordTrace (prefixWord ++ tailWord_2394738) baseStart_2394738 baseEnd_2394738 := by
    simpa [prefixWord, tailWord_2394738, baseEnd_2394738] using wordTrace_append hprefix tailTrace_2394738
  have hstable : (prefixWord ++ tailWord_2394738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394738).length < 2 ^ (prefixWord ++ tailWord_2394738).sum := by decide
  have hdescent : baseEnd_2394738 < baseStart_2394738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2394797 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_2394797 : Nat := 118140960795 + 2394797 * 2 ^ 59
def prefixEnd_2394797 : Nat := 4983230072969 + 3 ^ 40 * 2394797 * 2
def baseEnd_2394797 : Nat := 409893976981790693141345

theorem tailTrace_2394797 : CollatzResearch.WordTrace tailWord_2394797 prefixEnd_2394797 409893976981790693141345 := by
  unfold tailWord_2394797
  simp only [CollatzResearch.WordTrace]
  refine ⟨87345422305066942610654645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58230281536711295073769763 87345422305066942610654645)
  ·
    refine ⟨8188633341100025869748873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87345422305066942610654645 8188633341100025869748873)
    ·
      refine ⟨6141475005825019402311655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8188633341100025869748873 6141475005825019402311655)
      ·
        refine ⟨9212212508737529103467483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6141475005825019402311655 9212212508737529103467483)
        ·
          refine ⟨13818318763106293655201225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9212212508737529103467483 13818318763106293655201225)
          ·
            refine ⟨10363739072329720241400919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13818318763106293655201225 10363739072329720241400919)
            ·
              refine ⟨15545608608494580362101379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10363739072329720241400919 15545608608494580362101379)
              ·
                refine ⟨23318412912741870543152069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15545608608494580362101379 23318412912741870543152069)
                ·
                  refine ⟨4372202421139100726841013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23318412912741870543152069 4372202421139100726841013)
                  ·
                    refine ⟨409893976981790693141345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4372202421139100726841013 409893976981790693141345)
                    ·
                      rfl

theorem cell23_2394797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_2394797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2394797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2394797 prefixEnd_2394797 := by exact prefixLift 2394797
  have htrace : WordTrace (prefixWord ++ tailWord_2394797) baseStart_2394797 baseEnd_2394797 := by
    simpa [prefixWord, tailWord_2394797, baseEnd_2394797] using wordTrace_append hprefix tailTrace_2394797
  have hstable : (prefixWord ++ tailWord_2394797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2394797).length < 2 ^ (prefixWord ++ tailWord_2394797).sum := by decide
  have hdescent : baseEnd_2394797 < baseStart_2394797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2394797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
